# screensaver_app.py
# -*- coding: utf-8 -*-
import os
import sys
import json
import time
import random
import platform
import threading
import tkinter as tk
from tkinter import filedialog, messagebox, colorchooser
from typing import Optional
from PIL import Image, ImageTk

IS_WINDOWS = platform.system() == "Windows"
CONFIG_FILE = "config.json"
SUPPORTED_EXTS = (".png", ".jpg", ".jpeg", ".bmp", ".gif", ".tiff", ".webp")


# ---------------------- 기본 설정 ----------------------
def default_config():
    return {
        "mode": "single",                  # single | folder
        "image_path": "",                  # 파일 또는 폴더
        "timeout_seconds": 300,            # 유휴 시간(초)
        "slideshow_interval": 10,          # 폴더 슬라이드쇼 간격(초)
        "scale_mode": "fit",               # fit | fill | stretch
        "background": "#000000",           # 배경색
        "shuffle": True,                   # 폴더 슬라이드쇼 섞기
        "mouse_move_exit_pixels": 10,      # 종료 기준 마우스 이동 픽셀
        "allow_blank_single": True,        # 단일 모드에서 이미지 없을 때 배경만 실행 허용
        "clock_overlay": False,            # 배경만일 때 시계 오버레이 표시
        "start_in_tray": False             # 시작 시 트레이로만 실행(트레이 없으면 최소화)
    }


# ---------------------- Windows 유휴/모니터 ----------------------
if IS_WINDOWS:
    import ctypes
    from ctypes import wintypes
    import tkinter.messagebox as messagebox

    
    def is_already_running():
        mutex_name = "screensaver_app_unique_mutex"
        kernel32 = ctypes.windll.kernel32
        mutex = kernel32.CreateMutexW(None, False, mutex_name)
        last_error = kernel32.GetLastError()
        return last_error == 183  # ERROR_ALREADY_EXISTS

    if is_already_running():
        messagebox.showerror("중복 실행", "이미 프로그램이 실행 중입니다.")
        sys.exit(0)


    # DPI 스케일링 문제 해결: Per-monitor DPI awareness 설정
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        pass

def get_idle_seconds_windows() -> float:
    """
    Windows: GetLastInputInfo로 시스템 유휴 시간(초)
    """
    class LASTINPUTINFO(ctypes.Structure):
        _fields_ = [
            ("cbSize", ctypes.wintypes.UINT),
            ("dwTime", ctypes.wintypes.DWORD),
        ]
    lii = LASTINPUTINFO()
    lii.cbSize = ctypes.sizeof(LASTINPUTINFO)
    if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(lii)):
        return 0.0
    tick_count = ctypes.windll.kernel32.GetTickCount()
    idle_ms = tick_count - lii.dwTime
    return idle_ms / 1000.0


def enum_monitors_windows():
    """
    Windows: 모든 모니터 {left, top, width, height} 목록
    """
    monitors = []
    MonitorEnumProc = ctypes.WINFUNCTYPE(
        ctypes.wintypes.BOOL,
        ctypes.wintypes.HMONITOR,
        ctypes.wintypes.HDC,
        ctypes.POINTER(ctypes.wintypes.RECT),
        ctypes.wintypes.LPARAM
    )

    def _callback(hMonitor, hdcMonitor, lprcMonitor, dwData):
        r = lprcMonitor.contents
        left, top = r.left, r.top
        width, height = r.right - r.left, r.bottom - r.top
        monitors.append({"left": left, "top": top, "width": width, "height": height})
        return True

    ctypes.windll.user32.EnumDisplayMonitors(0, 0, MonitorEnumProc(_callback), 0)
    return monitors


def get_all_monitors():
    if IS_WINDOWS:
        mons = enum_monitors_windows()
        if mons:
            return mons
    # Fallback: 단일 화면
    root = tk._get_default_root()
    if root is None:
        temp = tk.Tk(); temp.withdraw()
        w, h = temp.winfo_screenwidth(), temp.winfo_screenheight()
        temp.destroy()
    else:
        w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    return [{"left": 0, "top": 0, "width": w, "height": h}]


def get_idle_seconds():
    if IS_WINDOWS:
        return get_idle_seconds_windows()
    # 기타 OS: 유휴 감지는 미지원(항상 0)
    return 0.0


# ---------------------- 이미지 유틸 ----------------------
def resize_image(img: Image.Image, target_w: int, target_h: int, scale_mode: str) -> Image.Image:
    if scale_mode == "stretch":
        return img.resize((target_w, target_h), Image.LANCZOS)

    iw, ih = img.size
    if iw == 0 or ih == 0:
        return img

    if scale_mode == "fit":
        # 전체가 보이도록(여백 발생 가능)
        ratio = min(target_w / iw, target_h / ih)
        nw, nh = int(iw * ratio), int(ih * ratio)
        return img.resize((nw, nh), Image.LANCZOS)

    if scale_mode == "fill":
        # 화면을 꽉 채우도록(잘림 가능)
        ratio = max(target_w / iw, target_h / ih)
        nw, nh = int(iw * ratio), int(ih * ratio)
        img2 = img.resize((nw, nh), Image.LANCZOS)
        left = (nw - target_w) // 2
        top = (nh - target_h) // 2
        return img2.crop((left, top, left + target_w, top + target_h))

    return img


def list_images_in_folder(folder: str):
    if not os.path.isdir(folder):
        return []
    files = []
    for name in os.listdir(folder):
        p = os.path.join(folder, name)
        if os.path.isfile(p) and os.path.splitext(name)[1].lower() in SUPPORTED_EXTS:
            files.append(p)
    return files


# ---------------------- 메인 앱 ----------------------
class ScreenSaverApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("화면보호기 설정")
        self.root.geometry("800x550")

        self.config = self.load_config()
        self.saver_active = False
        self.background_only = False
        self.saver_windows = []
        self.saver_labels = []
        self.current_images = []
        self.slideshow_index = 0
        self.slideshow_job = None
        self.idle_check_job = None
        self.clock_job = None
        self.activated_mouse_positions = {}
        self.activated_at = 0.0

        # 닫기(X): 종료가 아니라 트레이/최소화로 숨기기
        self.root.protocol("WM_DELETE_WINDOW", self.on_hide_to_tray)

        # UI 구성
        self.build_ui()

        # 트레이 준비(선택 기능)
        self.tray = None
        self.setup_tray_async()

        # 시작 시 트레이로만 / 최소화 옵션
        if self.config.get("start_in_tray", False):
            if self.tray:
                self.root.withdraw()
            else:
                # 트레이가 없으면 최소화로 작업 표시줄에 머물기
                self.root.iconify()

        # 유휴 감시 시작
        self.schedule_idle_check()

    # ---------------- UI ----------------
    def build_ui(self):
        frm = tk.Frame(self.root, padx=12, pady=12)
        frm.pack(fill="both", expand=True)

        # 모드
        mode_frame = tk.Frame(frm); mode_frame.pack(anchor="w")
        tk.Label(mode_frame, text="이미지 소스:").pack(side="left", padx=(0, 8))
        self.mode_var = tk.StringVar(value=self.config.get("mode", "single"))
        tk.Radiobutton(mode_frame, text="단일 이미지", variable=self.mode_var, value="single").pack(side="left")
        tk.Radiobutton(mode_frame, text="폴더(슬라이드쇼)", variable=self.mode_var, value="folder").pack(side="left")

        # 경로
        path_frame = tk.Frame(frm); path_frame.pack(fill="x", pady=(8, 0))
        tk.Label(path_frame, text="경로:").pack(side="left")
        self.path_entry = tk.Entry(path_frame)
        self.path_entry.insert(0, self.config.get("image_path", ""))
        self.path_entry.pack(side="left", fill="x", expand=True, padx=6)
        tk.Button(path_frame, text="찾아보기", command=self.select_path).pack(side="left")

        # 시간 옵션
        timeout_frame = tk.Frame(frm); timeout_frame.pack(anchor="w", pady=(12, 0))
        tk.Label(timeout_frame, text="대기 시간(초):").pack(side="left")
        self.timeout_entry = tk.Entry(timeout_frame, width=8)
        self.timeout_entry.insert(0, str(self.config.get("timeout_seconds", 300)))
        self.timeout_entry.pack(side="left", padx=6)

        slide_frame = tk.Frame(frm); slide_frame.pack(anchor="w", pady=(8, 0))
        tk.Label(slide_frame, text="슬라이드쇼 간격(초):").pack(side="left")
        self.slide_entry = tk.Entry(slide_frame, width=8)
        self.slide_entry.insert(0, str(self.config.get("slideshow_interval", 10)))
        self.slide_entry.pack(side="left", padx=6)

        # 배치/배경/셔플
        opt_frame = tk.Frame(frm); opt_frame.pack(anchor="w", pady=(8, 0))
        tk.Label(opt_frame, text="배치:").pack(side="left")
        self.scale_var = tk.StringVar(value=self.config.get("scale_mode", "fit"))
        tk.OptionMenu(opt_frame, self.scale_var, "fit", "fill", "stretch").pack(side="left", padx=6)

        tk.Label(opt_frame, text="배경색:").pack(side="left", padx=(12, 0))
        self.bg_preview = tk.Label(opt_frame, width=2, relief="groove", bg=self.config.get("background", "#000000"))
        self.bg_preview.pack(side="left", padx=6)
        tk.Button(opt_frame, text="선택", command=self.pick_color).pack(side="left")

        self.shuffle_var = tk.BooleanVar(value=self.config.get("shuffle", True))
        tk.Checkbutton(opt_frame, text="셔플(폴더)", variable=self.shuffle_var).pack(side="left", padx=(12, 0))

        # 추가 옵션
        extra_frame = tk.Frame(frm); extra_frame.pack(anchor="w", pady=(8, 0))
        self.allow_blank_var = tk.BooleanVar(value=self.config.get("allow_blank_single", True))
        tk.Checkbutton(extra_frame, text="단일 이미지가 없어도 배경만으로 실행 허용", variable=self.allow_blank_var).pack(anchor="w")
        self.clock_overlay_var = tk.BooleanVar(value=self.config.get("clock_overlay", False))
        tk.Checkbutton(extra_frame, text="배경만일 때 시계 오버레이 표시", variable=self.clock_overlay_var).pack(anchor="w")
        self.start_in_tray_var = tk.BooleanVar(value=self.config.get("start_in_tray", False))
        tk.Checkbutton(extra_frame, text="프로그램 시작 시 트레이로만 실행(트레이 없으면 최소화)", variable=self.start_in_tray_var).pack(anchor="w")

        # 동작 버튼
        btn_frame = tk.Frame(frm); btn_frame.pack(fill="x", pady=(16, 0))
        tk.Button(btn_frame, text="저장", command=self.save_config).pack(side="left")
        tk.Button(btn_frame, text="미리보기", command=lambda: self.activate_screensaver(preview=True)).pack(side="left", padx=8)
        tk.Button(btn_frame, text="지금 실행", command=lambda: self.activate_screensaver(preview=False)).pack(side="left", padx=8)
        tk.Button(btn_frame, text="닫기(트레이/최소화)", command=self.on_hide_to_tray).pack(side="right")

        note = tk.Label(frm, fg="#666", justify="left", anchor="w",
                        text="※ Windows에서 시스템 유휴 시간과 멀티 모니터를 감지합니다.\n"
                             "   단일 이미지가 없을 때 배경만으로 실행할 수 있으며, 시계 오버레이 옵션도 제공합니다.\n"
                             "   설정 창을 닫으면 프로그램은 종료되지 않고 트레이(또는 최소화)로 이동합니다.")
        note.pack(fill="x", pady=(12, 0))

    def pick_color(self):
        c = colorchooser.askcolor(initialcolor=self.bg_preview["bg"])
        if c and c[1]:
            self.bg_preview.configure(bg=c[1])

    def select_path(self):
        mode = self.mode_var.get()
        if mode == "single":
            path = filedialog.askopenfilename(filetypes=[
                ("Image Files", "*.png;*.jpg;*.jpeg;*.bmp;*.gif;*.tiff;*.webp"),
                ("All Files", "*.*")
            ])
        else:
            path = filedialog.askdirectory()
        if path:
            self.path_entry.delete(0, tk.END)
            self.path_entry.insert(0, path)

    # ---------------- 설정 ----------------
    def load_config(self):
        cfg = default_config()
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    old = json.load(f)
                    cfg.update(old or {})
            except Exception as e:
                print("설정 파일 로드 오류:", e)
        return cfg

    def save_config(self):
        try:
            cfg = {
                "mode": self.mode_var.get(),
                "image_path": self.path_entry.get().strip(),
                "timeout_seconds": int(self.timeout_entry.get()),
                "slideshow_interval": int(self.slide_entry.get()),
                "scale_mode": self.scale_var.get(),
                "background": self.bg_preview["bg"],
                "shuffle": bool(self.shuffle_var.get()),
                "mouse_move_exit_pixels": int(self.config.get("mouse_move_exit_pixels", 10)),
                "allow_blank_single": bool(self.allow_blank_var.get()),
                "clock_overlay": bool(self.clock_overlay_var.get()),
                "start_in_tray": bool(self.start_in_tray_var.get()),
            }
        except ValueError:
            messagebox.showerror("오류", "숫자 항목(대기 시간, 슬라이드쇼 간격)을 확인하세요.")
            return

        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        self.config = cfg
        messagebox.showinfo("저장 완료", "설정이 저장되었습니다.")

    # ---------------- 유휴 감시 ----------------
    def schedule_idle_check(self):
        if self.idle_check_job:
            self.root.after_cancel(self.idle_check_job)
        self.idle_check_job = self.root.after(1000, self.check_idle)

    def check_idle(self):
        try:
            if not self.saver_active:
                idle = get_idle_seconds()
                timeout = self.config.get("timeout_seconds", 300)
                if timeout > 0 and idle >= timeout:
                    self.activate_screensaver(preview=False)
        finally:
            self.schedule_idle_check()

    # ---------------- 화면보호기 ----------------
    def activate_screensaver(self, preview: bool = False):
        if self.saver_active:
            return

        
        # 루트 창에서도 키 입력 감지하도록 바인딩 추가
        self.root.bind("<Any-KeyPress>", self.exit_screensaver)

        # 현재 UI 값으로 설정 업데이트(저장버튼 안 눌러도 반영)
        try:
            self.config.update({
                "mode": self.mode_var.get(),
                "image_path": self.path_entry.get().strip(),
                "timeout_seconds": int(self.timeout_entry.get()),
                "slideshow_interval": int(self.slide_entry.get()),
                "scale_mode": self.scale_var.get(),
                "background": self.bg_preview["bg"],
                "shuffle": bool(self.shuffle_var.get()),
                "allow_blank_single": bool(self.allow_blank_var.get()),
                "clock_overlay": bool(self.clock_overlay_var.get()),
            })
        except ValueError:
            messagebox.showerror("오류", "숫자 항목(대기 시간, 슬라이드쇼 간격)을 확인하세요.")
            return

        # 이미지 목록 준비
        images = []
        mode = self.config["mode"]
        src = self.config["image_path"]
        self.background_only = False

        if mode == "single":
            if src and os.path.isfile(src):
                images = [src]
            else:
                if self.config.get("allow_blank_single", True):
                    self.background_only = True
                    images = [None]  # 센티넬
                else:
                    messagebox.showerror("오류", "유효한 이미지 파일을 선택하세요.")
                    return
        else:
            files = list_images_in_folder(src)
            if not files:
                messagebox.showerror("오류", "폴더에 표시할 이미지가 없습니다.")
                return
            if self.config.get("shuffle", True):
                random.shuffle(files)
            images = files

        self.current_images = images
        self.slideshow_index = 0

        # 미리보기 아니면 설정창 숨김
        if not preview:
            # 트레이가 있으면 완전 숨김, 없으면 최소화
            if self.tray:
                self.root.withdraw()
            else:
                self.root.iconify()

        # 멀티 모니터에 전체화면 창 생성
        self.saver_active = True
        self.saver_windows.clear()
        self.saver_labels.clear()
        self.activated_at = time.time()
        self.activated_mouse_positions.clear()

        for mon in get_all_monitors():
            win = tk.Toplevel(self.root)
            win.overrideredirect(True)
            win.attributes("-topmost", True)
            win.focus_force()
            win.grab_set()
            win.configure(bg=self.config.get("background", "#000000"), cursor="none")

            win.bind("<Key>", self.exit_screensaver)
            win.bind("<Any-KeyPress>", self.exit_screensaver)
            win.bind("<Any-ButtonPress>", self.exit_screensaver)
            win.bind("<Motion>", self.on_mouse_motion)

            if IS_WINDOWS:
                try:
                    win.attributes("-toolwindow", True)
                except Exception:
                    pass
            geom = f"{mon['width']}x{mon['height']}+{mon['left']}+{mon['top']}"
            win.geometry(geom)
            win.configure(bg=self.config.get("background", "#000000"))

            win.bind("<Any-KeyPress>", self.exit_screensaver)
            win.bind("<Any-ButtonPress>", self.exit_screensaver)
            win.bind("<Motion>", self.on_mouse_motion)

            label = tk.Label(win, bg=self.config.get("background", "#000000"))
            label.pack(fill="both", expand=True)

            # 중앙 정렬(시계 오버레이 대비)
            label.configure(anchor="center", justify="center")

            # 초기 마우스 위치
            try:
                x = win.winfo_pointerx()
                y = win.winfo_pointery()
                self.activated_mouse_positions[win] = (x, y)
            except Exception:
                self.activated_mouse_positions[win] = None

            self.saver_windows.append(win)
            self.saver_labels.append((label, mon))

        # 초기 프레임 표시
        self.show_current_image_on_all()

        # 슬라이드쇼 또는 시계 오버레이 스케줄
        if not self.background_only and len(self.current_images) > 1:
            self.schedule_slideshow()
        elif self.background_only and self.config.get("clock_overlay", False):
            self.schedule_clock_overlay()

    def schedule_slideshow(self):
        if self.slideshow_job:
            self.root.after_cancel(self.slideshow_job)
        interval_ms = max(1, int(self.config.get("slideshow_interval", 10))) * 1000
        self.slideshow_job = self.root.after(interval_ms, self.next_slide)

    def next_slide(self):
        if not self.saver_active:
            return
        self.slideshow_index = (self.slideshow_index + 1) % len(self.current_images)
        self.show_current_image_on_all()
        if len(self.current_images) > 1:
            self.schedule_slideshow()

    def open_image_safe(self, path: str) -> Optional[Image.Image]:
        try:
            img = Image.open(path)
            if getattr(img, "is_animated", False):
                img = img.convert("RGBA")
            else:
                img = img.convert("RGB")
            return img
        except Exception as e:
            print(f"이미지 열기 실패: {path} -> {e}")
            return None

    def show_current_image_on_all(self):
        if not self.saver_active or not self.current_images:
            return

        path = self.current_images[self.slideshow_index]
        bg = self.config.get("background", "#000000")
        scale_mode = self.config.get("scale_mode", "fit")

        # 배경만 표시(이미지 없음)
        if self.background_only or path is None:
            for label, mon in self.saver_labels:
                label.configure(image="", text="", bg=bg)
                label.image = None
            return

        base_img = self.open_image_safe(path)
        if base_img is None:
            for label, mon in self.saver_labels:
                label.configure(image="", text="", bg=bg)
                label.image = None
            return

        for label, mon in self.saver_labels:
            W, H = mon["width"], mon["height"]
            if scale_mode == "fit":
                resized = resize_image(base_img, W, H, "fit")
                canvas = Image.new("RGB", (W, H), bg)
                x = (W - resized.width) // 2
                y = (H - resized.height) // 2
                canvas.paste(resized, (x, y))
                final = canvas
            else:
                final = resize_image(base_img, W, H, scale_mode)

            photo = ImageTk.PhotoImage(final)
            label.configure(image=photo, text="", bg=bg)
            label.image = photo  # 참조 유지

    # ---------------- 시계 오버레이 ----------------
    def schedule_clock_overlay(self):
        if self.clock_job:
            self.root.after_cancel(self.clock_job)
        self.clock_job = self.root.after(1000, self.update_clock_overlay)

    def update_clock_overlay(self):
        if not self.saver_active or not (self.background_only and self.config.get("clock_overlay", False)):
            return
        bg = self.config.get("background", "#000000")
        now = time.strftime("%H:%M:%S")
        # 큰 폰트(환경에 따라 없을 수 있어 try/except)
        try:
            font = ("Segoe UI", 48, "bold")
        except Exception:
            font = ("Arial", 48, "bold")

        for label, mon in self.saver_labels:
            label.configure(text=now, fg="#FFFFFF", bg=bg, font=font)
        self.schedule_clock_overlay()

    # ---------------- 이벤트/종료 ----------------
    def on_mouse_motion(self, event):
        if not self.saver_active:
            return
        thr = int(self.config.get("mouse_move_exit_pixels", 10))
        if (time.time() - self.activated_at) < 0.2:

            return
        win = event.widget.winfo_toplevel()
        orig = self.activated_mouse_positions.get(win)
        if not orig:
            try:
                self.activated_mouse_positions[win] = (event.x_root, event.y_root)
            except Exception:
                pass
            return
        ox, oy = orig
        dx = abs(event.x_root - ox)
        dy = abs(event.y_root - oy)
        if dx >= thr or dy >= thr:
            self.exit_screensaver()

    def exit_screensaver(self, event=None):
        if not self.saver_active:
            return

        if self.slideshow_job:
            self.root.after_cancel(self.slideshow_job)
            self.slideshow_job = None

        if self.clock_job:
            self.root.after_cancel(self.clock_job)
            self.clock_job = None

        for w in list(self.saver_windows):
            try:
                if w.winfo_exists():
                    w.destroy()
            except Exception:
                pass
        self.saver_windows.clear()
        self.saver_labels.clear()
        self.saver_active = False

        # 설정 창 복원(트레이가 있으면 사용자가 아이콘으로 여는 걸 선호할 수 있어 복원하지 않음)
        if not self.tray:
                try:
                    if not self .root.winfo_viewable():
                        self.root.deiconify()
                        self.root.lift()
                except Exception:
                    pass

    # ---------------- 트레이 ----------------
    def setup_tray_async(self):
        """
        pystray가 설치되어 있으면 트레이 아이콘을 띄움.
        Tk를 막지 않도록 별도 스레드 실행.
        """
        try:
            import pystray
            from PIL import Image as PILImage, ImageDraw

            def create_icon():
                img = PILImage.new("RGBA", (64, 64), (0, 0, 0, 0))
                d = ImageDraw.Draw(img)
                d.rounded_rectangle((8, 8, 56, 56), radius=12, fill=(30, 144, 255, 255))
                d.rectangle((20, 24, 44, 40), fill=(255, 255, 255, 255))
                return img

            def on_open(icon, item):
                self.root.after(0, lambda: (self.root.deiconify(), self.root.lift()))

            def on_run_now(icon, item):
                self.root.after(0, lambda: self.activate_screensaver(preview=False))

            def on_exit(icon, item):
                self.root.after(0, self.on_exit_app)

            menu = pystray.Menu(
                pystray.MenuItem("설정 열기", on_open),
                pystray.MenuItem("지금 화면보호기 실행", on_run_now),
                pystray.MenuItem("종료", on_exit)
            )
            icon = pystray.Icon("screensaver", icon=create_icon(), title="화면보호기", menu=menu)
            self.tray = icon

            t = threading.Thread(target=icon.run, daemon=True)
            t.start()
        except Exception as e:
            # pystray가 없거나 실패해도 앱은 계속 동작
            print("트레이 비활성(선택 기능).", e)
            self.tray = None

    def on_hide_to_tray(self):
        """
        설정 창 닫기 → 종료 대신 트레이/최소화로 숨김.
        """
        try:
            if self.tray:
                self.root.withdraw()  # 트레이에서 다시 열 수 있음
            else:
                self.root.iconify()   # 트레이가 없으면 최소화하여 작업 표시줄에서 복원 가능
        except Exception:
            pass
    def on_exit_app(self):
        try:
            if self.tray:
                try:
                    self.tray.stop()
                except Exception:
                    pass
            self.exit_screensaver()
            if self.idle_check_job:
                self.root.after_cancel(self.idle_check_job)
            if self.clock_job:
                self.root.after_cancel(self.clock_job)
        finally:
            self.root.destroy()


# ---------------------- 엔트리 ----------------------
def main():
    root = tk.Tk()
    app = ScreenSaverApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()