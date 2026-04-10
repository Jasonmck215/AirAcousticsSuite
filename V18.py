import customtkinter as ctk
import tkinter as tk
import pyvisa, serial, serial.tools.list_ports
import time, threading, os, sys, webbrowser, pathlib, json, atexit, shutil
import gzip, pickle
from datetime import datetime
import numpy as np
from PIL import Image, ImageTk

import matplotlib
matplotlib.use('TkAgg')
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.widgets import SpanSelector
from scipy.signal import hilbert, spectrogram
from scipy.special import jn, j1, jn_zeros
import pywt  
from tkinter import filedialog, messagebox

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

WAVEFORMS  = {"Sine": "SINusoid", "Square": "SQUare", "Triangle": "TRIangle", "Ramp": "RAMP"}
TX_CHANNEL = "CHANnel1"   
RX_CHANNEL = "CHANnel2"   

# Standard bandwidth thresholds used in transducer characterization
BW_THRESHOLDS = {
    "-3 dB":  3.0,   # Half-power (most common)
    "-6 dB":  6.0,   # Half-pressure
    "-10 dB": 10.0,  # Common in sonar/ultrasound specs
    "-20 dB": 20.0,  # Full bandwidth floor
}

def get_appdata_dir():
    appdata = pathlib.Path(os.getenv('LOCALAPPDATA')) / "AirAcousticsSuite"
    appdata.mkdir(parents=True, exist_ok=True)
    return appdata

def resource_path(relative_path):
    try: 
        base_path = sys._MEIPASS
    except Exception: 
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

def make_label(parent, text, color=("black", "white"), size=11, bold=False):
    font = ("Arial", size, "bold") if bold else ("Arial", size)
    return ctk.CTkLabel(parent, text=text, font=font, text_color=color)

def section_sep(parent, text=""):
    make_label(parent, text or "─" * 30, color=("#1976d2", "#90caf9"), size=11, bold=True).pack(pady=(6, 1))

def labeled_entry(parent, label, default, width=120):
    make_label(parent, label).pack()
    e = ctk.CTkEntry(parent, width=width)
    if default: e.insert(0, default)
    e.pack(pady=3)
    return e

def two_column_entries(parent, label1, label2, default1="", default2=""):
    f = ctk.CTkFrame(parent, fg_color="transparent")
    f.pack(fill="x", padx=5)
    f.grid_columnconfigure((0, 1), weight=1)
    make_label(f, label1).grid(row=0, column=0)
    make_label(f, label2).grid(row=0, column=1)
    e1 = ctk.CTkEntry(f, width=110)
    if default1: e1.insert(0, default1)
    e1.grid(row=1, column=0, padx=5, pady=3)
    e2 = ctk.CTkEntry(f, width=110)
    if default2: e2.insert(0, default2)
    e2.grid(row=1, column=1, padx=5, pady=3)
    return e1, e2

def labeled_seg(parent, label, values, default, **kwargs):
    make_label(parent, label).pack(pady=(4, 0))
    s = ctk.CTkSegmentedButton(parent, values=values, **kwargs)
    s.set(default)
    s.pack(pady=3, padx=5, fill="x")
    return s

def drive_voltage_row(parent):
    """Voltage empty by default — persisted via settings."""
    return two_column_entries(parent, "Voltage (V)", "Cycles", "", "5")

def render_math(parent, tex_string, size=16, mode="Dark"):
    bg_color = '#2b2b2b' if mode == 'Dark' else '#e0e0e0'
    text_color = 'white' if mode == 'Dark' else 'black'
    fig = Figure(figsize=(7, 0.8), facecolor=bg_color) 
    fig.text(0.05, 0.5, tex_string, fontsize=size, color=text_color, va='center')
    canvas = FigureCanvasTkAgg(fig, master=parent)
    widget = canvas.get_tk_widget()
    widget.pack(anchor="w", pady=(0, 10))
    return widget

# ------------------------------------------------------------------
# ISO 9613-1 Atmospheric Absorption
# ------------------------------------------------------------------
def atmospheric_absorption_db_per_m(freq_hz, temp_c, humidity_pct, pressure_kpa=101.325):
    """Calculate atmospheric absorption coefficient in dB/m per ISO 9613-1."""
    if humidity_pct <= 0 or freq_hz <= 0:
        return 0.0
    T = temp_c + 273.15
    T_ref = 293.15
    T_01 = 273.16
    p_ref = 101.325
    pr = pressure_kpa / p_ref
    
    C = -6.8346 * (T_01 / T) ** 1.261 + 4.6151
    h = humidity_pct * (10 ** C) * pr
    
    f_rO = pr * (24.0 + 4.04e4 * h * (0.02 + h) / (0.391 + h))
    f_rN = pr * (T / T_ref) ** (-0.5) * (9.0 + 280.0 * h * np.exp(-4.170 * ((T / T_ref) ** (-1.0/3.0) - 1.0)))
    
    f = freq_hz
    alpha = 8.686 * f * f * (
        1.84e-11 / pr * (T / T_ref) ** 0.5 +
        (T / T_ref) ** (-2.5) * (
            0.01275 * np.exp(-2239.1 / T) / (f_rO + f * f / f_rO) +
            0.1068 * np.exp(-3352.0 / T) / (f_rN + f * f / f_rN)
        )
    )
    return float(alpha)

class AirAcousticsSuite(ctk.CTk):
    def __init__(self):
        super().__init__()
        self._load_on_start = None
        if len(sys.argv) > 1 and sys.argv[1].endswith('.aas'):
            self._load_on_start = sys.argv[1]

        self.title("Air Acoustics Suite 1.0")
        self.geometry("1400x850")
        self.minsize(1200, 750)
        
        self._apply_window_icon(self)
        self.withdraw() 
        self.protocol("WM_DELETE_WINDOW", self.on_closing)

        self.scope, self.fg, self.arduino = None, None, None
        self.rm = None 
        self.is_running = False

        self._current_aas_file = None  # Tracks the currently loaded/saved .aas file
        self._is_dirty = False         # Tracks if there are unsaved changes

        self.last_burst_t      = None; self.last_burst_tx    = None; self.last_burst_mic   = None
        self.last_burst_fft_f  = None; self.last_burst_fft_m = None
        self.last_sweep_data   = None; self.last_polar_data  = None
        self.last_cwt_raw      = None; self.last_adv_raw     = None
        self._last_fg_state    = None
        self.imp_data          = {}

        self._last_burst_kwargs = {}
        self._last_sw_bw_kwargs = {}
        self._last_polar_kwargs = {}
        self._last_adv_kwargs   = {}
        self._last_cwt_kwargs   = {}

        self._noise_override   = None
        self._last_noise_rms   = None
        self._last_noise_range = None
        self._calibrated_noise_rms = 0.0 # Baseline OSC noise floor
        self._last_burst_pre_list = None
        self._last_burst_env2  = None
        
        self._clipping_warn_time = 0
        self.last_activity_time = time.time()
        self.INACTIVITY_TIMEOUT = 600

        self._paned_windows = []  
        self._tk_frames = []
        self._fullscreen_windows = {}

        atexit.register(self.emergency_hardware_release)
        self._setup_menus()
        self.show_splash_screen()
        self.after(5000, self.check_inactivity)

    def _apply_window_icon(self, window):
        icon_path = resource_path("icon.ico")
        if os.path.exists(icon_path):
            try: 
                window.iconbitmap(default=icon_path)
                window.iconbitmap(icon_path)
            except Exception: pass

    def _ping_activity(self):
        self.last_activity_time = time.time()

    def check_inactivity(self):
        if not self.is_running and self.rm is not None:
            if time.time() - self.last_activity_time > self.INACTIVITY_TIMEOUT:
                self.log("Idle for 10 minutes. Auto-disconnecting hardware to prevent USB lock-ups.")
                self.emergency_hardware_release()
                self.ind_fg.configure(text="💤 FG Sleep", text_color="gray")
                self.ind_scp.configure(text="💤 Scope Sleep", text_color="gray")
                self.ind_mot.configure(text="💤 Motor Sleep", text_color="gray")
        self.after(5000, self.check_inactivity)

    def emergency_hardware_release(self):
        try:
            if self.fg:
                self.fg.timeout = 200
                try: self.fg.write("OUTPut1:STATe OFF") 
                except: pass
                self.fg.close(); self.fg = None
        except Exception: pass 
        try:
            if self.scope:
                self.scope.timeout = 200
                self.scope.close(); self.scope = None
        except Exception: pass
        try:
            if self.arduino:
                self.arduino.close(); self.arduino = None
        except Exception: pass
        try:
            if self.rm:
                self.rm.close(); self.rm = None
        except Exception: pass

    def on_closing(self):
        if not self.check_dirty_and_prompt("closing the application"): return
        
        self.is_running = False 
        self.save_settings(); self.withdraw()
        for key in list(self._fullscreen_windows.keys()):
            try: self._fullscreen_windows[key].destroy()
            except: pass
        try: plt.close('all')
        except: pass
        threading.Thread(target=self.emergency_hardware_release, daemon=True).start()
        self.after(500, lambda: os._exit(0))

    def toggle_theme(self):
        current_mode = ctk.get_appearance_mode()
        new_mode = "Light" if current_mode == "Dark" else "Dark"
        ctk.set_appearance_mode(new_mode)
        self.btn_theme.configure(text="🌙 Dark Mode" if new_mode == "Light" else "☀️ Light Mode")
        pw_bg = "#d9d9d9" if new_mode == "Light" else "#333333"
        frm_bg = "#ebebeb" if new_mode == "Light" else "#242424"
        for pw in self._paned_windows: pw.configure(bg=pw_bg)
        for f in self._tk_frames: f.configure(bg=frm_bg)
        self._apply_window_icon(self)
        for w in self._fullscreen_windows.values():
            try: self._apply_window_icon(w)
            except: pass

    def _get_current_settings_dict(self):
        return {
            "temp": self.temp_entry.get(), "mic_sens": self.mic_sens.get(), "mod_gain": self.module_gain.get(),
            "humidity": self.humidity_entry.get(), "ref_dist": self.ref_dist_entry.get(), "ref_dist_lock": self.ref_dist_lock_var.get(),
            "burst_voltage": self.burst_voltage.get(), "burst_cycles": self.burst_cycles.get(),
            "sweep_voltage": self.sweep_voltage.get(), "polar_voltage": self.polar_voltage.get(),
            "adv_voltage": self.adv_voltage.get(), "adv_cycles": self.adv_cycles.get(),
            "cwt_voltage": self.cwt_voltage.get(), "cwt_cycles": self.cwt_cycles.get(),
            "imp_fmin": self.imp_fmin.get(), "imp_fmax": self.imp_fmax.get(),
            "imp_type": self.imp_type.get(), "imp_x_scale": self.imp_x_scale.get(), "imp_y_scale": self.imp_y_scale.get(),
            "cal_noise": self._calibrated_noise_rms,
            "pred_geom": self.pred_geom.get() if hasattr(self, 'pred_geom') else "Circular",
            "pred_dim": self.pred_dim.get() if hasattr(self, 'pred_dim') else "10.0",
            "pred_mode_n": self.pred_mode_n.get() if hasattr(self, 'pred_mode_n') else "0",
            "pred_mode_m": self.pred_mode_m.get() if hasattr(self, 'pred_mode_m') else "0",
            "burst_sep": self.burst_sep_slider.get() if hasattr(self, 'burst_sep_slider') else 4.0,
            
            # New Advanced Settings mapping
            "cwt_acq": self.cwt_acq.get() if hasattr(self, 'cwt_acq') else "Average",
            "cwt_avg_n": self.cwt_avg_n.get() if hasattr(self, 'cwt_avg_n') else "128",
            "cwt_settle": self.cwt_settle.get() if hasattr(self, 'cwt_settle') else "0.5",
            
            "adv_acq": self.adv_acq.get() if hasattr(self, 'adv_acq') else "Average",
            "adv_avg_n": self.adv_avg_n.get() if hasattr(self, 'adv_avg_n') else "128",
            "adv_settle": self.adv_settle.get() if hasattr(self, 'adv_settle') else "0.5",
            
            "burst_settle": self.burst_settle.get() if hasattr(self, 'burst_settle') else "0.2"
        }

    def _apply_settings_dict(self, settings):
        def _set(entry, key):
            if key in settings and settings[key] is not None:
                if isinstance(entry, ctk.CTkEntry):
                    entry.delete(0, 'end'); entry.insert(0, str(settings[key]))
                elif isinstance(entry, ctk.BooleanVar):
                    entry.set(settings[key])
                elif isinstance(entry, ctk.CTkSegmentedButton):
                    entry.set(settings[key])
        _set(self.temp_entry, "temp"); _set(self.mic_sens, "mic_sens"); _set(self.module_gain, "mod_gain")
        _set(self.humidity_entry, "humidity"); _set(self.ref_dist_entry, "ref_dist")
        if "ref_dist_lock" in settings: self.ref_dist_lock_var.set(settings["ref_dist_lock"])
        _set(self.burst_voltage, "burst_voltage"); _set(self.burst_cycles, "burst_cycles")
        _set(self.sweep_voltage, "sweep_voltage"); _set(self.polar_voltage, "polar_voltage")
        _set(self.adv_voltage, "adv_voltage"); _set(self.adv_cycles, "adv_cycles")
        _set(self.cwt_voltage, "cwt_voltage"); _set(self.cwt_cycles, "cwt_cycles")
        _set(self.imp_fmin, "imp_fmin"); _set(self.imp_fmax, "imp_fmax")
        _set(self.imp_type, "imp_type"); _set(self.imp_x_scale, "imp_x_scale"); _set(self.imp_y_scale, "imp_y_scale")
        if "cal_noise" in settings: self._calibrated_noise_rms = float(settings["cal_noise"])
        if "pred_geom" in settings: self.pred_geom.set(settings["pred_geom"])
        if "pred_dim" in settings: self.pred_dim.delete(0, 'end'); self.pred_dim.insert(0, str(settings["pred_dim"]))
        if "pred_mode_n" in settings: _set(self.pred_mode_n, "pred_mode_n")
        if "pred_mode_m" in settings: _set(self.pred_mode_m, "pred_mode_m")
        if "burst_sep" in settings and hasattr(self, 'burst_sep_slider'): self.burst_sep_slider.set(float(settings["burst_sep"]))
        
        # New Advanced Settings Application
        if "cwt_acq" in settings and hasattr(self, 'cwt_acq'): _set(self.cwt_acq, "cwt_acq")
        if "cwt_avg_n" in settings and hasattr(self, 'cwt_avg_n'): _set(self.cwt_avg_n, "cwt_avg_n")
        if "cwt_settle" in settings and hasattr(self, 'cwt_settle'): _set(self.cwt_settle, "cwt_settle")
        
        if "adv_acq" in settings and hasattr(self, 'adv_acq'): _set(self.adv_acq, "adv_acq")
        if "adv_avg_n" in settings and hasattr(self, 'adv_avg_n'): _set(self.adv_avg_n, "adv_avg_n")
        if "adv_settle" in settings and hasattr(self, 'adv_settle'): _set(self.adv_settle, "adv_settle")
        
        if "burst_settle" in settings and hasattr(self, 'burst_settle'): _set(self.burst_settle, "burst_settle")
        
        self._update_eff_sens_label()

    def save_settings(self):
        try:
            with open(get_appdata_dir() / "settings.json", "w") as f: json.dump(self._get_current_settings_dict(), f)
        except: pass

    def load_settings(self):
        try:
            file_path = get_appdata_dir() / "settings.json"
            if file_path.exists():
                with open(file_path, "r") as f: self._apply_settings_dict(json.load(f))
        except: pass

    def _get_dash_state(self):
        return {
            'vpp': self.dash_vpp.cget('text'), 'pa': self.dash_pa.cget('text'), 'spl': self.dash_spl.cget('text'),
            'sl': self.dash_sl.cget('text'), 'snr': self.dash_snr.cget('text'), 'dist': self.dash_dist.cget('text'),
            'thd': self.dash_thd.cget('text'), 'tau': self.dash_tau.cget('text'), 'peak_f': self.dash_peak_f.cget('text'),
            'bw': self.dash_bw.cget('text'), 'bw_title': self.dash_bw_title.cget('text'), 'q': self.dash_q.cget('text'),
            'bw3': self.dash_bw3.cget('text'), 'bw6': self.dash_bw6.cget('text')
        }
        
    def _set_dash_state(self, d):
        self.dash_vpp.configure(text=d.get('vpp', '-- V')); self.dash_pa.configure(text=d.get('pa', '-- Pa'))
        self.dash_spl.configure(text=d.get('spl', '-- dB SPL')); self.dash_sl.configure(text=d.get('sl', 'SL@1m: --'))
        self.dash_snr.configure(text=d.get('snr', '-- dB SNR')); self.dash_dist.configure(text=d.get('dist', '-- cm'))
        self.dash_thd.configure(text=d.get('thd', 'THD: --%')); self.dash_tau.configure(text=d.get('tau', 'τ₂₀: -- ms'))
        self.dash_peak_f.configure(text=d.get('peak_f', '-- kHz')); self.dash_bw.configure(text=d.get('bw', '-- kHz'))
        self.dash_bw_title.configure(text=d.get('bw_title', 'Bandwidth (-6dB)')); self.dash_q.configure(text=d.get('q', '--'))
        self.dash_bw3.configure(text=d.get('bw3', '-- °')); self.dash_bw6.configure(text=d.get('bw6', '-- °'))

    def _setup_menus(self):
        self.topbar = ctk.CTkFrame(self, height=35, fg_color=("#e0e0e0", "#242424"), corner_radius=0)
        self.topbar.pack(side="top", fill="x")
        btn_style = {"fg_color":"transparent", "hover_color":("#c9c9c9", "#3a3a3a"), "font":("Arial", 12, "bold")}
        
        # --- File Dropdown Menu ---
        self.file_btn = ctk.CTkButton(self.topbar, text="📁 File", text_color=("black", "white"), **btn_style)
        self.file_btn.pack(side="left", padx=10, pady=5)
        
        self.file_menu = tk.Menu(self, tearoff=0, font=("Arial", 11))
        self.file_menu.add_command(label="📝 New File", command=self.new_file)
        self.file_menu.add_command(label="📂 Load .AAS File", command=self.load_aas_file_dialog)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="💾 Save (.aas)", command=self.save_aas)
        self.file_menu.add_command(label="💾 Save As (.aas)", command=self.save_as_aas)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="📊 Export All Plots", command=lambda: self._export_workflow("Export Plots", save_plots=True))
        self.file_menu.add_command(label="📉 Export All Raw Data", command=lambda: self._export_workflow("Export Raw Data", save_csvs=True))
        self.file_menu.add_command(label="📦 Export All Data and .aas", command=lambda: self._export_workflow("Export All Data", save_plots=True, save_csvs=True, save_aas=True))
        
        def show_file_menu(event):
            try: self.file_menu.tk_popup(self.file_btn.winfo_rootx(), self.file_btn.winfo_rooty() + self.file_btn.winfo_height())
            finally: self.file_menu.grab_release()
            
        self.file_btn.bind("<Button-1>", show_file_menu)

        ctk.CTkButton(self.topbar, text="📚 Documentation", text_color=("#1976d2", "#90caf9"), command=self.show_docs, **btn_style).pack(side="left", padx=10, pady=5)
        ctk.CTkButton(self.topbar, text="⚠️ Keysight Software", text_color=("#e65100", "#ffcc00"), command=self.show_driver_warning, **btn_style).pack(side="left", padx=10, pady=5)
        ctk.CTkButton(self.topbar, text="⚖️ License & Liability", text_color=("#455a64", "#b0bec5"), command=lambda: self.show_license(force=True), **btn_style).pack(side="left", padx=10, pady=5)
        self.btn_theme = ctk.CTkButton(self.topbar, text="☀️ Light Mode", text_color=("black", "white"), command=self.toggle_theme, **btn_style)
        self.btn_theme.pack(side="right", padx=10, pady=5)

    def show_license(self, force=False, on_accept=None):
        win = ctk.CTkToplevel(self); win.title("License & Liability"); win.geometry("500x550")
        self._apply_window_icon(win)
        win.attributes('-topmost', True); win.grab_set()
        
        png_path = resource_path("splash.png"); jpg_path = resource_path("splash.jpg")
        try:
            if os.path.exists(png_path): img = Image.open(png_path).convert("RGBA")
            elif os.path.exists(jpg_path): img = Image.open(jpg_path).convert("RGBA")
            else: raise FileNotFoundError
            img_w, img_h = img.size; max_w, max_h = 400, 200
            ratio = min(max_w / img_w, max_h / img_h)
            new_size = (int(img_w * ratio), int(img_h * ratio))
            ctk_img = ctk.CTkImage(light_image=img, dark_image=img, size=new_size)
            ctk_img_lbl = ctk.CTkLabel(win, text="", image=ctk_img)
            ctk_img_lbl.pack(pady=(20, 10))
        except Exception: pass
            
        text = ("AIR ACOUSTICS SUITE - ACADEMIC USE\n\nThis software is provided 'as-is' for university research. "
                "The author assumes NO RESPONSIBILITY for: (including but not limited to)\n\n1. Errors in data analysis or calculations.\n"
                "2. Damage to transducers or hardware.\n3. Loss of experimental data.\n\n"
                "Verification against manual scope measurements is always recommended.")
        ctk.CTkLabel(win, text=text, wraplength=400, justify="left").pack(padx=20, pady=(10, 20))
        def accept():
            with open(get_appdata_dir() / "license_accepted.txt", "w") as f: f.write("accepted")
            win.grab_release(); win.destroy()
            if on_accept: on_accept()
        ctk.CTkButton(win, text="Dismiss" if force else "I Accept & Understand", command=accept).pack(pady=10)

    def show_docs(self):
        win = ctk.CTkToplevel(self); win.title("Science & Math Documentation"); win.geometry("500x550")
        self._apply_window_icon(win); win.attributes('-topmost', True)
        scroll = ctk.CTkScrollableFrame(win, width=460, height=510, fg_color=("#e0e0e0", "#2b2b2b"))
        scroll.pack(fill="both", expand=True, padx=10, pady=10)
        make_label(scroll, "📐 FORMULAS & CONCEPTS", size=18, bold=True, color=("#1976d2", "#90caf9")).pack(anchor="w", pady=(10, 5), padx=10)

        docs = [
            ("1. Speed of Sound Correction", "Corrected for ambient temperature T (°C). Essential for accurate Time-of-Flight distance calculations.", r"$c = 331.3 \sqrt{1 + \frac{T}{273.15}} \text{ m/s}$"),
            ("2. Acoustic Pressure", "Converts raw scope voltage to actual physical sound pressure. Note: S_eff combines your Mic Sensitivity and Module Gain into one value.", r"$P_{rms} = \frac{V_{rms}}{S_{eff}}$"),
            ("3. Sound Pressure Level (SPL)", "Converts linear pressure into a logarithmic decibel scale relative to the standard human hearing threshold (20 µPa).", r"$SPL = 20 \log_{10}\left(\frac{P_{rms}}{20 \times 10^{-6}}\right) \text{ dB}$"),
            ("4. Atmospheric Absorption (ISO 9613-1)", "High frequencies (ultrasound) lose significant energy to the air depending on humidity. This accounts for that loss per meter.", r"$\alpha(f, T, h) \text{ dB/m — applied over measured distance}$"),
            ("5. Source Level at 1m", "The 'gold standard' metric for comparing transducers. It calculates what the SPL *would be* exactly 1m away by adding back distance (spreading) and air absorption losses.", r"$SL = SPL_{meas} + 20\log_{10}(d) + \alpha \cdot d$"),
            ("6. Envelope Detection (Hilbert)", "Math trick using the Hilbert transform to draw a smooth curve over the raw AC sound wave. Used to precisely find the arrival time of a sound burst.", r"$Env(t) = \sqrt{V(t)^2 + \mathcal{H}\{V(t)\}^2}$"),
            ("7. Time-of-Flight (ToF)", "Calculates the distance between the transmitter and receiver by timing how long the sound burst took to travel through the air.", r"$d = c \cdot (t_{rx} - t_{tx})$"),
            ("8. Ring-Down Time (τ)", "How long the transducer keeps 'ringing' after the electrical drive stops. A long ring-down usually means a high Q-factor.", r"$\tau_{20dB} \approx \frac{Q}{\pi f_0} \text{ (theoretical)}$"),
            ("9. Signal-to-Noise Ratio (SNR)", "Compares the actual sound signal strength to the background room noise. High SNR (>20 dB) means clean, reliable data.", r"$SNR = 20 \log_{10}\left(\frac{\sigma_{signal}}{\sigma_{noise}}\right) \text{ dB}$"),
            ("10. Total Harmonic Distortion (THD)", "Measures if the transducer is being over-driven. If you apply too much voltage, it generates unwanted harmonic frequencies instead of pure sound.", r"$THD = \frac{\sqrt{V_2^2 + V_3^2 + \cdots}}{V_1} \times 100\%$"),
            ("11. Bandwidth (-NdB)", "The usable frequency range of the transducer. -3dB (half-power) is standard, but -6dB (half-pressure) is also common.", r"$BW_N = f_{upper,N} - f_{lower,N}$"),
            ("12. Mechanical Quality Factor (Q)", "Describes how 'sharp' the resonance is. High Q means it rings a long time but has a very narrow usable frequency band.", r"$Q = \frac{f_{peak}}{BW_{-3dB}}$"),
            ("13. Polar Directivity", "Shows how focused the sound beam is. Calculates the angle between the left and right points where the sound pressure drops by 3dB or 6dB.", r"$\theta_{BW} = |\theta_{right} - \theta_{left}|$"),
            ("14. STFT Spectrogram", "Visualizes how the frequency content of the sound changes over time. Great for seeing harmonics and frequency shifts during long ring-downs.", r"$STFT(t, \omega) = \int x(\tau) w(\tau - t) e^{-j\omega \tau} d\tau$"),
            ("15. Wavelet Transform (CWT)", "Similar to STFT but with variable resolution. Excellent for analyzing very short, transient ultrasound pulses.", r"$CWT(a, b) = \frac{1}{\sqrt{a}} \int x(t) \psi^*\left(\frac{t - b}{a}\right) dt$"),
            ("16. HIFFUT Flexural Pattern (n, m)", "Edge-clamped flexural radiation (HIFFUT). n = radial nodes, m = angular nodes. (0,0) is fundamental flexural mode.", r"$D(\theta) \propto \left| \frac{J_{m}(ka \sin\theta)}{(j_{m,n+1})^2 - (ka \sin\theta)^2} \right|$"),
            ("17. Rectangular Pattern (n, m)", "Flexural mode radiation along primary axis. n = nodal lines. n=0 is fundamental.", r"$D(\theta) \propto \left| \frac{\cos(X) \text{ or } \sin(X)}{X^2 - ((n+1)\pi/2)^2} \right|$")
        ]
        current_mode = ctk.get_appearance_mode(); body_labels = []
        for title, body, math_str in docs:
            make_label(scroll, title, size=15, bold=True, color=("#1976d2", "#90caf9")).pack(anchor="w", pady=(15, 3), padx=10)
            lbl = ctk.CTkLabel(scroll, text=body, justify="left", wraplength=400, font=("Arial", 13), text_color=("black", "white"))
            lbl.pack(anchor="w", pady=(0, 5), padx=20); body_labels.append(lbl)
            render_math(scroll, math_str, mode=current_mode) 

        def _on_doc_resize(event):
            if event.widget == win:
                new_wrap = max(200, win.winfo_width() - 90)
                for label in body_labels:
                    try: label.configure(wraplength=new_wrap)
                    except: pass
        win.bind("<Configure>", _on_doc_resize)

    def show_splash_screen(self):
        self.splash = tk.Toplevel(self); self.splash.overrideredirect(True); self.splash.attributes('-topmost', True)
        self._apply_window_icon(self.splash); self.splash.configure(bg="#000001")
        try: self.splash.attributes("-transparentcolor", "#000001")
        except: pass
        self.splash.withdraw()
        png_path = resource_path("splash.png"); jpg_path = resource_path("splash.jpg")
        try:
            if os.path.exists(png_path): img = Image.open(png_path).convert("RGBA")
            elif os.path.exists(jpg_path): img = Image.open(jpg_path).convert("RGBA")
            else: raise FileNotFoundError
            img_w, img_h = img.size; max_w, max_h = 800, 600
            if img_w > max_w or img_h > max_h:
                ratio = min(max_w / img_w, max_h / img_h)
                img = img.resize((int(img_w * ratio), int(img_h * ratio)), Image.Resampling.LANCZOS)
            self.splash_image = ImageTk.PhotoImage(img)
            self.splash_lbl = tk.Label(self.splash, image=self.splash_image, bg="#000001", bd=0)
            self.splash_lbl.pack(fill="both", expand=True)
        except Exception:
            self.splash.configure(bg="#242424")
            ctk.CTkLabel(self.splash, text="Air Acoustics Suite", font=("Arial", 36, "bold"), text_color="#90caf9").place(relx=0.5, rely=0.4, anchor="center")
            ctk.CTkLabel(self.splash, text="Loading...", font=("Arial", 14), text_color="gray").place(relx=0.5, rely=0.55, anchor="center")
        self.splash.update_idletasks()
        sw, sh = self.splash.winfo_screenwidth(), self.splash.winfo_screenheight()
        ww, wh = self.splash.winfo_reqwidth(), self.splash.winfo_reqheight()
        self.splash.geometry(f'{ww}x{wh}+{int((sw/2)-(ww/2))}+{int((sh/2)-(wh/2))}')
        self.splash.deiconify(); self.splash.update()
        self.setup_ui(); self.load_settings()
        self.after(6000, self.close_splash_screen)

    def close_splash_screen(self):
        self.splash.destroy(); self.deiconify()
        self.update_idletasks(); self.after(250, self._maximize_window)
        self.after(500, self.check_startup_sequence)

    def check_startup_sequence(self):
        if not (get_appdata_dir() / "license_accepted.txt").exists(): 
            self.show_license(force=False, on_accept=self._check_auto_load)
        else: self._check_auto_load()
            
    def _check_auto_load(self):
        if self._load_on_start and os.path.exists(self._load_on_start):
            self.after(500, lambda: self.load_aas_file(self._load_on_start))

    def launch_keysight_installer(self):
        app_dir = os.path.dirname(sys.executable) if getattr(sys, 'frozen', False) else os.path.dirname(os.path.abspath(__file__))
        installer_path = os.path.join(app_dir, "Keysight IO Library Suite Installer.exe")
        if os.path.exists(installer_path):
            try: os.startfile(installer_path)
            except Exception as e: webbrowser.open("https://www.keysight.com/us/en/lib/software-detail/computer-software/io-libraries-suite-downloads-2175637.html")
        else: webbrowser.open("https://www.keysight.com/us/en/lib/software-detail/computer-software/io-libraries-suite-downloads-2175637.html")

    def show_driver_warning(self):
        warn_win = ctk.CTkToplevel(self); warn_win.title("Important Hardware Notice"); warn_win.geometry("600x200")
        self._apply_window_icon(warn_win); warn_win.attributes('-topmost', True); warn_win.grab_set()
        try: warn_win.eval(f'tk::PlaceWindow {str(warn_win)} center')
        except: pass
        ctk.CTkLabel(warn_win, text="To connect to hardware, this PC requires\nthe Keysight IO Libraries Suite.", font=("Arial", 14)).pack(pady=(25, 15))
        ctk.CTkButton(warn_win, text="Install Keysight IO Suite", fg_color="#1f538d", command=self.launch_keysight_installer).pack(pady=15)
        ctk.CTkButton(warn_win, text="Close", command=lambda: (warn_win.grab_release(), warn_win.destroy()), width=120, fg_color="#2b7a78").pack(pady=5)

    def _maximize_window(self):
        try: self.state('zoomed')
        except: 
            try: self.attributes('-zoomed', True)
            except: pass

    # ------------------------------------------------------------------
    # Hardware Connection
    # ------------------------------------------------------------------
    def init_hw(self):
        self._ping_activity()
        self.ind_fg.configure(text="⏳ FG", text_color="orange")
        self.ind_scp.configure(text="⏳ Scope", text_color="orange")
        self.ind_mot.configure(text="⏳ Motor", text_color="orange"); self.update()
        try:
            if self.rm is None:
                try:
                    try: self.rm = pyvisa.ResourceManager('@ktvisa')
                    except: self.rm = pyvisa.ResourceManager()
                except: 
                    self.show_driver_warning()
                    self.ind_fg.configure(text="🔴 Fail", text_color="gray")
                    self.ind_scp.configure(text="🔴 Fail", text_color="gray")
                    self.ind_mot.configure(text="🔴 Fail", text_color="gray")
                    return
                    
            res = self.rm.list_resources()
            
            # --- FG Connection ---
            try:
                if self.fg is None:
                    self.fg = self.rm.open_resource([r for r in res if "0x0699" in r][0])
                    self.fg.clear(); time.sleep(0.2)
                self.ind_fg.configure(text="🟢 FG OK", text_color="#00E676")
            except: self.ind_fg.configure(text="🔴 FG Fail", text_color="#ff5252")
                
            # --- Scope Connection ---
            try:
                if self.scope is None:
                    self.scope = self.rm.open_resource([r for r in res if "0x0957" in r or "0x2A8D" in r][0])
                    self.scope.clear(); time.sleep(0.2)
                    self.scope.timeout = 5000 # Default pyvisa timeout
                self.ind_scp.configure(text="🟢 Scope OK", text_color="#00E676")
            except: self.ind_scp.configure(text="🔴 Scope Fail", text_color="#ff5252")

            # --- Motor Connection ---
            try:
                # 1. Ping existing connection to see if it's alive
                if self.arduino is not None:
                    try:
                        self.arduino.in_waiting # Safe hardware ping
                        self.ind_mot.configure(text="🟢 Motor OK", text_color="#00E676")
                    except:
                        self.arduino = None # Connection died
                
                # 2. If dead or none, find it
                if self.arduino is None:
                    connected = False
                    for p in serial.tools.list_ports.comports():
                        if any(x in p.description for x in ["Arduino", "USB Serial", "CH340"]):
                            self.arduino = serial.Serial(p.device, 9600, timeout=1); time.sleep(1); self.arduino.write(b"Z\n")
                            connected = True; break
                    if connected: self.ind_mot.configure(text="🟢 Motor OK", text_color="#00E676")
                    else: self.ind_mot.configure(text="🔴 Motor Fail", text_color="#ff5252")
            except: self.ind_mot.configure(text="🔴 Motor Fail", text_color="#ff5252")

            self.log("Hardware connection sequence finished.")
        except Exception as e: self.log(f"HW Sys Fail: {e}")

    def universal_stop(self):
        self.is_running = False
        try:
            if self.fg: self.fg.write("OUTPut1:STATe OFF")
        except: pass
        self.log("Stopped.")

    def log(self, msg):
        self.log_box.insert("end", f"> {msg}\n"); self.log_box.see("end")

    def check_dirty_and_prompt(self, action_name):
        """Checks if data is unsaved and prompts the user before wiping it."""
        if self._is_dirty:
            res = messagebox.askyesnocancel("Unsaved Changes", f"You have unsaved data.\n\nDo you want to save before {action_name}?")
            if res is True:
                self.save_aas()
                if self._is_dirty: return False # If save failed or was canceled during dialog, abort action
            elif res is None:
                return False # User canceled the action entirely
        return True

    def new_file(self):
        """Clears out all graphs, data caches, and starts a fresh blank canvas."""
        if not self.check_dirty_and_prompt("creating a new file"): return
        
        # Reset internal data state
        self.last_burst_t = None; self.last_burst_tx = None; self.last_burst_mic = None
        self.last_burst_fft_f = None; self.last_burst_fft_m = None
        self.last_sweep_data = None; self.last_polar_data = None
        self.last_cwt_raw = None; self.last_adv_raw = None
        self._last_fg_state = None
        self._polar_overlays = []
        self._current_aas_file = None
        
        # Clear Dashboard
        empty_dash = {'vpp': '-- V', 'pa': '-- Pa', 'spl': '-- dB SPL', 'sl': 'SL@1m: --', 'snr': '-- dB SNR', 'dist': '-- cm', 'thd': 'THD: --%', 'tau': 'τ₂₀: -- ms', 'peak_f': '-- kHz', 'bw': '-- kHz', 'bw_title': 'Bandwidth (-6dB)', 'q': '--', 'bw3': '-- °', 'bw6': '-- °'}
        self._set_dash_state(empty_dash)
        
        # Clear UI Plots safely
        self.fig_b.clf(); self.canvas_b.draw()
        self.ax_sw.clear(); self.ax_sw.set_title("Waiting...", fontsize=10, color="gray")
        self.clear_bw_plot(); self.canvas_sw.draw()
        self._clear_polar()
        self.fig_adv.clf(); self.canvas_adv.draw()
        self.fig_cwt.clf(); self.canvas_cwt.draw()
        
        # Clear Impedance
        self.imp_data.clear()
        self.update_imp_listbox()
        self.update_imp_plot()
        
        self._is_dirty = False
        self.log("Started a new blank workspace.")

    def jog_motor(self, d):
        self._ping_activity()
        if self.arduino: self.arduino.write(f"J{d}\n".encode())
        
    def set_new_center(self):
        self._ping_activity()
        if self.arduino: self.arduino.write(b"S\n")

    def _effective_sens_v_pa(self):
        try: return (float(self.mic_sens.get()) / 1000.0) * (10 ** (float(self.module_gain.get()) / 20.0))
        except ValueError: return 1.0

    def _update_eff_sens_label(self):
        try: self.eff_sens_lbl.configure(text=f"Effective: {self._effective_sens_v_pa()*1000:.2f} mV/Pa")
        except: self.eff_sens_lbl.configure(text="Effective: --")

    def _set_ui_state(self, running):
        state = "disabled" if running else "normal"
        self.btn_run_burst.configure(state=state, text="⏳ RUNNING..." if running else "▶ RUN")
        self.btn_run_sweep.configure(state=state, text="⏳ RUNNING..." if running else "▶ START SWEEP")
        self.btn_run_polar.configure(state=state, text="⏳ RUNNING..." if running else "▶ START SCAN")
        self.btn_run_adv.configure(state=state, text="⏳ RUNNING..." if running else "▶ RUN STFT")
        self.btn_run_cwt.configure(state=state, text="⏳ RUNNING..." if running else "▶ RUN CWT")

    # ------------------------------------------------------------------
    # Scope Smart Auto-Scale (RX Only)
    # ------------------------------------------------------------------
    def smart_autoscale_rx(self, on_complete=None, target_f_hz=None, target_v=None, target_w=None, target_mode=None):
        if not self.scope or not self.fg:
            self.log("Hardware not connected.")
            return
        self._ping_activity()
        threading.Thread(target=self._autoscale_worker, args=(on_complete, target_f_hz, target_v, target_w, target_mode), daemon=True).start()

    def _autoscale_worker(self, on_complete, target_f_hz, target_v, target_w, target_mode):
        try:
            self.is_running = True; self._set_ui_state(True)
            self.log("Auto-scaling RX (CH2)...")
            
            mode = target_mode if target_mode else self.burst_fg_mode.get()
            wf = target_w if target_w else WAVEFORMS.get(self.burst_wave.get(), "SINusoid")
            freq_hz = target_f_hz if target_f_hz is not None else float(self.burst_f.get() or "40") * 1000
            volt = target_v if target_v else (self.burst_voltage.get() or "5")
            cycles = self.burst_cycles.get() or "5"
            scales = [0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0]
            
            if mode == "Burst":
                self.log("Scaling using Burst signal to match ring-up...")
                self._fg_set_burst(freq_hz, volt, cycles, waveform=wf)
            else:
                self.log("Scaling using Continuous signal...")
                self._fg_set_continuous(waveform=wf, voltage=volt)
                self.fg.write(f"SOURCE1:FREQUENCY {freq_hz}")
                
            self.fg.write("OUTPut1:STATe ON")
            time.sleep(0.2)
                
            for _ in range(6):
                if not self.is_running: break
                try: current_scale = float(self.scope.query(f":{RX_CHANNEL}:SCALe?"))
                except: break
                
                if mode == "Burst":
                    self._scope_set_acquire("Normal")
                    self.scope.write(f":DIGitize {TX_CHANNEL},{RX_CHANNEL}")
                    pre, mic_v, is_clip, span_pct = self._scope_read_channel_raw(RX_CHANNEL)
                else:
                    self.scope.write(":RUN")
                    time.sleep(0.5)
                    vpp = self._scope_measure_cw(RX_CHANNEL, "Vpp")
                    span_pct = min(1.0, vpp / (current_scale * 8.0))
                    is_clip = span_pct >= 0.95

                self.after(0, lambda sp=span_pct, ic=is_clip: self._update_level_meter(sp, ic))
                
                if is_clip or span_pct > 0.95:
                    next_scales = [s for s in scales if s > current_scale * 1.05]
                    if not next_scales: break
                    self.scope.write(f":{RX_CHANNEL}:SCALe {next_scales[0]}")
                    time.sleep(0.3)
                elif span_pct < 0.2:
                    target_scale = (current_scale * span_pct * 8) / 5.0 
                    next_scales = [s for s in scales if s >= target_scale]
                    new_scale = next_scales[0] if next_scales else current_scale
                    if new_scale >= current_scale: break
                    self.scope.write(f":{RX_CHANNEL}:SCALe {new_scale}")
                    time.sleep(0.3)
                else:
                    self.log(f"Perfect scale found: {current_scale} V/div")
                    break
                    
            self.fg.write("OUTPut1:STATe OFF")
            self._last_fg_state = None 
        except Exception as e:
            self.log(f"Auto-scale err: {e}")
        finally:
            try: self.fg.write("OUTPut1:STATe OFF")
            except: pass
            self._set_ui_state(False)
            if on_complete: self.after(500, on_complete)

    def _update_level_meter(self, span_pct, is_clipping):
        self.clip_bar.set(span_pct)
        if is_clipping: self.clip_bar.configure(progress_color="#ff5252")
        elif span_pct > 0.8: self.clip_bar.configure(progress_color="#FF9800")
        else: self.clip_bar.configure(progress_color="#4CAF50")

    def show_clipping_warning(self, restart_callback=None, clip_f_hz=None, clip_v=None, clip_w=None, clip_mode=None):
        now = time.time()
        if now - self._clipping_warn_time < 5.0 and restart_callback is None: return
        self._clipping_warn_time = now
        
        warn_win = ctk.CTkToplevel(self); warn_win.title("⚠️ SIGNAL CLIPPING DETECTED"); warn_win.geometry("550x240")
        self._apply_window_icon(warn_win); warn_win.attributes('-topmost', True); warn_win.grab_set()
        try: warn_win.eval(f'tk::PlaceWindow {str(warn_win)} center')
        except: pass
        
        ctk.CTkLabel(warn_win, text="⚠️ The received signal is clipping the Oscilloscope ADC!", font=("Arial", 16, "bold"), text_color="#ff5252").pack(pady=(25, 5))
        
        if restart_callback:
            ctk.CTkLabel(warn_win, text="The scan was automatically aborted to prevent recording bad data.\nWould you like the software to Auto-Scale the oscilloscope\nand automatically restart the scan?", font=("Arial", 13)).pack(pady=10)
            btn_frame = ctk.CTkFrame(warn_win, fg_color="transparent"); btn_frame.pack(fill="x", pady=(5, 10))
            def do_auto_restart():
                warn_win.grab_release(); warn_win.destroy()
                self.smart_autoscale_rx(on_complete=restart_callback, target_f_hz=clip_f_hz, target_v=clip_v, target_w=clip_w, target_mode=clip_mode)
            ctk.CTkButton(btn_frame, text="⚡ Auto-Scale & Restart Scan", fg_color="#2e7d32", hover_color="#1b5e20", font=("Arial", 12, "bold"), command=do_auto_restart).pack(side="left", padx=(40, 10), expand=True)
            ctk.CTkButton(btn_frame, text="Cancel", fg_color="#c62828", hover_color="#b71c1c", font=("Arial", 12, "bold"), command=lambda: (warn_win.grab_release(), warn_win.destroy())).pack(side="right", padx=(10, 40), expand=True)
        else:
            ctk.CTkLabel(warn_win, text="Your measurements (Vpp, SPL, THD) will be highly inaccurate.\n\nPlease either:\n1) Reduce the Transducer Drive Voltage\n2) Click the '⚡ Smart Auto-Scale RX' button.", font=("Arial", 12)).pack(pady=10)
            ctk.CTkButton(warn_win, text="Understood", fg_color="#c62828", command=lambda: (warn_win.grab_release(), warn_win.destroy())).pack(pady=10)

    # ------------------------------------------------------------------
    # Fullscreen & Plots
    # ------------------------------------------------------------------
    def _fullscreen_plot(self, source_fig, title="Plot"):
        if hasattr(self, '_is_fs') and self._is_fs: return
        self._is_fs = True
        
        # Hide navigation elements so the plot fills the screen natively
        self.topbar.pack_forget()
        self.sidebar.pack_forget()
        
        try: self.tabs._segmented_button.grid_remove()
        except: pass
        
        # FIX: Only hide the control panel of the tab currently visible on the screen!
        self._saved_pane_widths = {}
        for left_frame in self._tk_frames:
            if left_frame.winfo_ismapped():  # Only true if this tab is actively open
                pw = left_frame.master
                try:
                    w = left_frame.winfo_width()
                    self._saved_pane_widths[left_frame] = w if w >= 250 else 320
                    pw.forget(left_frame)
                except: pass
            
        # Put a floating close button directly on the current tab
        current_tab = self.tabs.tab(self.tabs.get())
        self._fs_close_btn = ctk.CTkButton(current_tab, text="✖ EXIT FULLSCREEN (ESC)", 
                                           fg_color="#c62828", hover_color="#b71c1c", 
                                           font=("Arial", 12, "bold"),
                                           command=self._exit_fullscreen, height=32, width=200)
        self._fs_close_btn.place(relx=0.99, rely=0.98, anchor="se")
        
        self.bind("<Escape>", self._exit_fullscreen)
        source_fig.canvas.draw_idle()

    def _exit_fullscreen(self, event=None):
        if not getattr(self, '_is_fs', False): return
        self._is_fs = False
        
        if hasattr(self, '_fs_close_btn') and self._fs_close_btn:
            self._fs_close_btn.destroy()
        
        # Restore Topbar and Sidebar natively
        self.topbar.pack(side="top", fill="x", before=self.main_container)
        self.sidebar.pack(side="left", fill="y", padx=(8, 0), pady=8, before=self.tabs)
        
        try: self.tabs._segmented_button.grid()
        except: pass
        
        # FIX: Only restore the specific control panel(s) that we actually hid
        for left_frame, w in getattr(self, '_saved_pane_widths', {}).items():
            pw = left_frame.master
            try:
                panes = pw.panes()
                if panes:
                    plot_frame = pw.nametowidget(panes[0]) if isinstance(panes[0], str) else panes[0]
                    pw.add(left_frame, before=plot_frame, minsize=250, width=w)
                else:
                    pw.add(left_frame, minsize=250, width=w)
                
                self.after(50, lambda p=pw, width=w: p.sash_place(0, width, 0))
            except: pass
            
        self._saved_pane_widths = {} # Clear the cache
        
        self.unbind("<Escape>")
        # Force redraw of all canvases so they snap back to their grid sizes
        for fig in [self.fig_b, self.fig_sw, self.fig_p, self.fig_adv, self.fig_cwt, self.fig_imp]:
            try: fig.canvas.draw_idle()
            except: pass

    def _add_fullscreen_btn(self, toolbar_parent, fig, title):
        btn = tk.Button(toolbar_parent, text="⛶ Fullscreen", font=("Arial", 9), relief="flat", bg="#444444", fg="white", activebackground="#666666", cursor="hand2", command=lambda: self._fullscreen_plot(fig, title))
        btn.pack(side="right", padx=6, pady=2)

    def _make_labels_editable(self, *axes):
        """Makes titles and axis labels clickable for editing across multiple axes."""
        for ax in axes:
            if ax is None: continue
            try:
                if ax.title: ax.title.set_picker(5)
                if ax.xaxis.label: ax.xaxis.label.set_picker(5)
                if ax.yaxis.label: ax.yaxis.label.set_picker(5)
            except Exception: pass

    def _open_text_editor(self, text_artist, canvas):
        """Pops up a rich text styling menu when a plot label is clicked."""
        # Prevent opening multiple overlapping dialogs
        if hasattr(self, '_text_dialog') and self._text_dialog and self._text_dialog.winfo_exists():
            self._text_dialog.destroy()
            
        self._text_dialog = ctk.CTkToplevel(self)
        self._text_dialog.title("Edit Plot Label")
        self._text_dialog.geometry("380x300")
        self._text_dialog.transient(self)
        self._text_dialog.grab_set()

        ctk.CTkLabel(self._text_dialog, text="Label Text:", font=("Arial", 12, "bold")).pack(pady=(15, 2))
        text_var = tk.StringVar(value=text_artist.get_text())
        ctk.CTkEntry(self._text_dialog, textvariable=text_var, width=320).pack(pady=(0, 15))

        # --- Font Family & Size Row ---
        row1 = ctk.CTkFrame(self._text_dialog, fg_color="transparent")
        row1.pack(fill="x", padx=30, pady=5)
        
        ctk.CTkLabel(row1, text="Font:").pack(side="left", padx=(0, 5))
        current_font = text_artist.get_fontfamily()
        if isinstance(current_font, list): current_font = current_font[0]
        
        font_var = tk.StringVar(value=current_font)
        fonts = ["sans-serif", "serif", "Arial", "Times New Roman", "Courier New", "Verdana", "Tahoma"]
        ctk.CTkOptionMenu(row1, variable=font_var, values=fonts, width=140).pack(side="left", padx=(0, 15))

        ctk.CTkLabel(row1, text="Size:").pack(side="left", padx=(0, 5))
        size_var = tk.StringVar(value=str(text_artist.get_fontsize()))
        ctk.CTkEntry(row1, textvariable=size_var, width=60).pack(side="left")

        # --- Bold & Italics Row ---
        row2 = ctk.CTkFrame(self._text_dialog, fg_color="transparent")
        row2.pack(fill="x", padx=30, pady=15)
        
        bold_var = tk.BooleanVar(value=(text_artist.get_fontweight() in ['bold', 'heavy', 'black', 700, 800, 900]))
        ctk.CTkCheckBox(row2, text="Bold", variable=bold_var).pack(side="left", padx=(20, 15))
        
        italic_var = tk.BooleanVar(value=(text_artist.get_fontstyle() in ['italic', 'oblique']))
        ctk.CTkCheckBox(row2, text="Italic", variable=italic_var).pack(side="left", padx=15)

        def save_changes():
            text_artist.set_text(text_var.get())
            text_artist.set_fontfamily(font_var.get())
            try: text_artist.set_fontsize(float(size_var.get()))
            except ValueError: pass # Ignore if they type text into the size box
            text_artist.set_fontweight('bold' if bold_var.get() else 'normal')
            text_artist.set_fontstyle('italic' if italic_var.get() else 'normal')
            
            canvas.draw_idle()
            self._is_dirty = True
            self._text_dialog.destroy()

        ctk.CTkButton(self._text_dialog, text="💾 APPLY STYLING", fg_color="#2e7d32", hover_color="#1b5e20", font=("Arial", 12, "bold"), command=save_changes).pack(pady=(10, 20))

    def _bind_custom_home(self, toolbar, fig):
        original_home = toolbar.home
        def custom_home(*args, **kwargs):
            self._restore_all_legends(fig)
            original_home(*args, **kwargs)
        toolbar.home = custom_home
        try:
            if hasattr(toolbar, '_buttons') and 'Home' in toolbar._buttons:
                toolbar._buttons['Home'].configure(command=custom_home)
            elif hasattr(toolbar, 'winfo_children'):
                for child in toolbar.winfo_children():
                    if isinstance(child, tk.Button) and 'home' in str(child.cget('command')).lower():
                        child.configure(command=custom_home)
        except Exception: pass

    def _restore_all_legends(self, fig):
        for ax in fig.get_axes():
            to_remove = []
            for item in ax.get_children():
                if getattr(item, '_is_thd_box', False): item.set_visible(True)
                elif getattr(item, '_is_custom_marker', False): to_remove.append(item)
            for item in to_remove:
                try: item.remove()
                except: pass
            master_handles = getattr(ax, '_master_handles', [])
            master_labels = getattr(ax, '_master_labels', [])
            if not master_handles: continue
            for h in master_handles:
                if isinstance(h, (list, tuple)):
                    for o in h: o.set_visible(True)
                else: h.set_visible(True)
            loc = getattr(ax, '_leg_loc', 'best'); fs = getattr(ax, '_leg_fs', 7)
            leg = ax.legend(master_handles, master_labels, loc=loc, fontsize=fs)
            self._make_legend_interactive(leg, master_handles, ax)
        fig.canvas.draw()

    def _make_legend_interactive(self, leg, handles, ax):
        if leg is None or not handles: return
        try:
            leg_items = getattr(leg, 'legend_handles', getattr(leg, 'legendHandles', []))
            leg_texts = leg.get_texts()
            for i in range(min(len(leg_items), len(leg_texts), len(handles))):
                leg_obj = leg_items[i]; text_obj = leg_texts[i]; orig_obj = handles[i]
                leg_obj.set_picker(5); text_obj.set_picker(5)
                state = {'orig': orig_obj, 'ax': ax}
                leg_obj._leg_state = state; text_obj._leg_state = state
        except Exception: pass

    def _on_legend_pick(self, event):
        item = event.artist
        import matplotlib.text as mtext
        if getattr(item, '_is_custom_marker', False):
            try:
                if hasattr(item, '_linked') and item._linked in item.axes.get_children(): item._linked.remove()
                item.remove(); event.canvas.draw()
            except Exception: pass
            return
        if getattr(item, '_is_thd_box', False):
            item.set_visible(False); event.canvas.draw(); return
            
        # FIX: Check if the user clicked a Title or Axis Label first
        if isinstance(item, mtext.Text) and not hasattr(item, '_leg_state'):
            self._open_text_editor(item, event.canvas)
            return
            
        if hasattr(item, '_leg_state'):
            state = item._leg_state; orig = state['orig']; ax = state['ax']
            
            # 1. Hide the actual plot element
            if isinstance(orig, (list, tuple)):
                for o in orig: o.set_visible(False)
            else: orig.set_visible(False)
            
            # 2. Rebuild the legend dynamically with only the visible items so the box shrinks!
            master_handles = getattr(ax, '_master_handles', [])
            master_labels = getattr(ax, '_master_labels', [])
            if master_handles:
                vis_handles, vis_labels = [], []
                for h, l in zip(master_handles, master_labels):
                    is_vis = h[0].get_visible() if isinstance(h, (list, tuple)) else h.get_visible()
                    if is_vis:
                        vis_handles.append(h)
                        vis_labels.append(l)
                
                if leg := ax.get_legend():
                    leg.remove()
                    
                if vis_handles:
                    loc = getattr(ax, '_leg_loc', 'best'); fs = getattr(ax, '_leg_fs', 7)
                    new_leg = ax.legend(vis_handles, vis_labels, loc=loc, fontsize=fs)
                    self._make_legend_interactive(new_leg, vis_handles, ax)
                    
            event.canvas.draw()

    def _on_plot_click(self, event):
        if event.dblclick and event.button == 1 and event.inaxes:
            ax = event.inaxes; x, y = event.xdata, event.ydata
            if x is None or y is None: return
            snap_x, snap_y = x, y
            if ax.name != 'polar' and ax.lines:
                try:
                    click_disp = ax.transData.transform((x, y)); min_dist = float('inf')
                    for line in ax.lines:
                        if not line.get_visible() or getattr(line, '_is_custom_marker', False): continue
                        xdata, ydata = line.get_xdata(), line.get_ydata()
                        if len(xdata) == 0: continue
                        idx = np.searchsorted(xdata, x)
                        if idx == len(xdata): idx -= 1
                        elif idx > 0 and abs(x - xdata[idx-1]) < abs(x - xdata[idx]): idx -= 1
                        lx, ly = xdata[idx], ydata[idx]
                        line_disp = ax.transData.transform((lx, ly))
                        dist = np.hypot(click_disp[0] - line_disp[0], click_disp[1] - line_disp[1])
                        if dist < min_dist and dist < 40:
                            min_dist = dist; snap_x, snap_y = lx, ly
                    x, y = snap_x, snap_y
                except Exception: pass
            
            def get_unit(label_text):
                if not label_text: return ""
                if '(' in label_text and ')' in label_text:
                    u = label_text[label_text.rfind('(')+1:label_text.rfind(')')]
                    return "dB" if "dB" in u else u
                return ""
                
            if ax.name == 'polar':
                lbl = f"{np.degrees(x) % 360:.1f}°, {y:.1f} dB"
            else:
                xu, yu = get_unit(ax.get_xlabel()), get_unit(ax.get_ylabel())
                lbl = f"{x:.3f}{f' {xu}' if xu else ''},  {y:.3f}{f' {yu}' if yu else ''}"
                
            pt, = ax.plot(x, y, 'ro', markersize=6, markeredgecolor='white', picker=5, zorder=999)
            txt = ax.text(x, y, f"  {lbl}", color='white', fontsize=10, fontweight='bold', bbox=dict(facecolor='#d84315', alpha=0.9, edgecolor='none', boxstyle='round,pad=0.3'), picker=5, zorder=999, va='center')
            pt._is_custom_marker = True; txt._is_custom_marker = True
            pt._linked = txt; txt._linked = pt
            event.canvas.draw()

    # ------------------------------------------------------------------
    # Analytics Tools
    # ------------------------------------------------------------------
    def _auto_noise_rms(self, mic_v, env, pre_list):
        if self._noise_override is not None:
            s, e = self._noise_override
            s = max(0, min(s, len(mic_v)-1)); e = max(s+1, min(e, len(mic_v)))
            nr = np.std(mic_v[s:e]) if (e-s) > 10 else float(pre_list[1][7])
            return (nr if nr > 1e-12 else float(pre_list[1][7])), s, e
        peak_env = np.max(env)
        if peak_env < 1e-12: return float(pre_list[1][7]), 0, min(500, len(mic_v))
        active = np.where(env > peak_env * 0.05)[0]
        if len(active) == 0: return float(pre_list[1][7]), 0, min(500, len(mic_v))
        sig_s, sig_e = active[0], active[-1]; margin = 50
        pre_s, pre_e = margin, max(margin+1, sig_s - margin)
        post_s, post_e = min(sig_e + margin, len(mic_v)-margin-1), len(mic_v)-margin
        pl, psl = pre_e - pre_s, post_e - post_s
        if pl >= psl and pl >= 100: s, e = pre_s, pre_e
        elif psl >= 100: s, e = post_s, post_e
        elif pl >= 50: s, e = pre_s, pre_e
        elif psl >= 50: s, e = post_s, post_e
        else: s, e = 0, min(200, len(mic_v))
        nr = np.std(mic_v[s:e]) if (e-s) > 10 else float(pre_list[1][7])
        return (nr if nr > 1e-12 else float(pre_list[1][7])), s, e

    def _open_noise_selector(self):
        if self.last_burst_mic is None: return self.log("No burst data — run a burst first.")
        mic_v = self.last_burst_mic; t = self.last_burst_t; tm = t * 1000; env = np.abs(hilbert(mic_v))
        eff_v_pa = self._effective_sens_v_pa()
        win = tk.Toplevel(self); win.title("Noise Floor Selector — Click & Drag")
        self._apply_window_icon(win)
        try: win.state('zoomed')
        except: win.attributes('-zoomed', True)
        info_frame = tk.Frame(win, bg="#1a1a2e", height=60); info_frame.pack(fill="x", side="top"); info_frame.pack_propagate(False)
        tk.Label(info_frame, text="  DRAG to select noise region  │  ESC to cancel", bg="#1a1a2e", fg="#90caf9", font=("Arial", 12, "bold")).pack(side="left", padx=15, pady=5)
        result_var = tk.StringVar(value="")
        tk.Label(info_frame, textvariable=result_var, bg="#1a1a2e", fg="#00E676", font=("Consolas", 13, "bold")).pack(side="right", padx=20, pady=5)
        btn_frame = tk.Frame(win, bg="#1a1a2e", height=50); btn_frame.pack(fill="x", side="bottom"); btn_frame.pack_propagate(False)
        selected_range = [None, None]
        def apply_and_close():
            if selected_range[0] is not None:
                self._noise_override = (selected_range[0], selected_range[1])
                self.log(f"Noise override: [{selected_range[0]}:{selected_range[1]}]")
                self.noise_info_lbl.configure(text=f"σ: {np.std(mic_v[selected_range[0]:selected_range[1]]):.6f} V [manual]", text_color=("#e65100", "#ffcc00"))
                self._recompute_burst_with_noise()
            win.destroy()
        def reset_auto():
            self._noise_override = None; self.noise_info_lbl.configure(text="σ: auto", text_color=("gray40", "gray70"))
            self._recompute_burst_with_noise(); win.destroy()
        tk.Button(btn_frame, text="✓ APPLY", font=("Arial", 13, "bold"), bg="#2e7d32", fg="white", relief="flat", padx=30, command=apply_and_close).pack(side="left", padx=20, pady=8)
        tk.Button(btn_frame, text="↺ RESET AUTO", font=("Arial", 12), bg="#555", fg="white", relief="flat", padx=10, command=reset_auto).pack(side="left", padx=10, pady=8)
        tk.Button(btn_frame, text="✕ CANCEL", font=("Arial", 12), bg="#942121", fg="white", relief="flat", padx=20, command=win.destroy).pack(side="right", padx=20, pady=8)
        fig = Figure(figsize=(16, 9), facecolor='white')
        gs = fig.add_gridspec(3, 1, height_ratios=[2, 1.5, 1.5], hspace=0.35)
        ax_full = fig.add_subplot(gs[0]); ax_pre = fig.add_subplot(gs[1]); ax_post = fig.add_subplot(gs[2])
        active = np.where(env > np.max(env) * 0.05)[0]
        sig_s = active[0] if len(active) > 0 else len(mic_v)//3
        sig_e = active[-1] if len(active) > 0 else 2*len(mic_v)//3
        if self._noise_override: ns, ne = self._noise_override
        elif self._last_noise_range: ns, ne = self._last_noise_range
        else: _, ns, ne = self._auto_noise_rms(mic_v, env, self._last_burst_pre_list or [['0']*10]*2)
        for ax, s_idx, e_idx, title_t in [(ax_full, 0, len(tm), "Full Capture"), (ax_pre, 0, min(sig_s+200, len(tm)), "Pre-Signal (zoomed)"), (ax_post, max(0, sig_e-200), len(tm), "Post-Signal (zoomed)")]:
            ax.plot(tm[s_idx:e_idx], mic_v[s_idx:e_idx]/eff_v_pa, color='#1565c0', lw=0.4)
            ax.plot(tm[s_idx:e_idx], env[s_idx:e_idx]/eff_v_pa, color='red', lw=0.8, alpha=0.6)
            ax.axvspan(tm[ns], tm[min(ne-1, len(tm)-1)], color='#4caf50', alpha=0.25)
            ax.set_title(title_t, fontsize=10, fontweight='bold'); ax.set_ylabel("Pa"); ax.set_xlabel("Time (ms)"); ax.grid(True, alpha=0.2)
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=win); NavigationToolbar2Tk(canvas, win).update()
        canvas.get_tk_widget().pack(fill="both", expand=True)
        def on_select(vmin_ms, vmax_ms):
            i0 = int(np.searchsorted(tm, vmin_ms)); i1 = int(np.searchsorted(tm, vmax_ms))
            i0 = max(0, i0); i1 = min(len(mic_v), i1)
            if i1-i0 < 10: return
            selected_range[:] = [i0, i1]
            nr = np.std(mic_v[i0:i1]); snr = 20*np.log10(np.std(mic_v)/nr) if nr > 0 else 0
            result_var.set(f"σ={nr:.6f}V  [{i0}:{i1}]  SNR={snr:.1f}dB")
        spans = [SpanSelector(ax, on_select, 'horizontal', props=dict(facecolor='#4caf50', alpha=0.3), interactive=True, useblit=True) for ax in [ax_full, ax_pre, ax_post]]
        win._spans = spans; win.bind("<Escape>", lambda e: win.destroy()); canvas.draw()

    def _open_noise_calibration(self):
        """Pops up a window to measure the baseline system noise with the transducer disconnected."""
        if not self.scope:
            return self.log("Hardware not connected.")
            
        win = ctk.CTkToplevel(self)
        win.title("Baseline Noise Calibration")
        win.geometry("450x300")
        self._apply_window_icon(win)
        win.attributes('-topmost', True); win.grab_set()

        ctk.CTkLabel(win, text="BASELINE SYSTEM CALIBRATION", font=("Arial", 14, "bold"), text_color="#90caf9").pack(pady=(20, 10))
        ctk.CTkLabel(win, text="1. Disconnect the Transmitter (TX) transducer.\n2. Ensure the Receiver (RX) cable is connected.\n3. Click 'Measure' to capture oscilloscope noise floor.", justify="left", wraplength=400).pack(pady=10)

        status_lbl = ctk.CTkLabel(win, text=f"Current Baseline: {self._calibrated_noise_rms*1000:.4f} mV RMS", font=("Arial", 11), text_color="gray")
        status_lbl.pack(pady=10)

        def do_measure():
            btn_cal.configure(state="disabled", text="⏳ MEASURING...")
            self.after(100, lambda: self._run_noise_calibration_worker(win, status_lbl, btn_cal))

        btn_cal = ctk.CTkButton(win, text="▶ MEASURE BASELINE", fg_color="#2e7d32", command=do_measure)
        btn_cal.pack(pady=10)
        ctk.CTkButton(win, text="Close", command=lambda: (win.grab_release(), win.destroy())).pack(pady=10)

    def _run_noise_calibration_worker(self, win, status_lbl, btn_cal):
        try:
            # 1. Force FG OFF
            if self.fg: self.fg.write("OUTPut1:STATe OFF")
            time.sleep(0.5)

            # 2. Capture baseline noise from Scope
            self._scope_set_acquire("Average", 32)
            self.scope.timeout = 120000 # Give plenty of time
            self.scope.write(f":DIGitize {RX_CHANNEL}")
            pre, noise_volt, is_clip, span_pct = self._scope_read_channel_raw(RX_CHANNEL)
            
            # 3. Calculate baseline RMS
            self._calibrated_noise_rms = np.std(noise_volt)
            self._is_dirty = True
            
            status_lbl.configure(text=f"Measured Baseline: {self._calibrated_noise_rms*1000:.4f} mV RMS", text_color="#00E676")
            self.log(f"Noise floor calibrated to: {self._calibrated_noise_rms:.6f} V RMS")
        except Exception as e:
            self.log(f"Calib fail: {e}")
            status_lbl.configure(text="Measurement Failed!", text_color="#ff5252")
        finally:
            if self.scope: self.scope.timeout = 5000
            btn_cal.configure(state="normal", text="▶ RE-MEASURE")

    def _recompute_burst_with_noise(self):
        if self.last_burst_mic is None: return
        mic_v = self.last_burst_mic; t = self.last_burst_t; tx_v = self.last_burst_tx
        eff_v_pa = self._effective_sens_v_pa(); pre_list = self._last_burst_pre_list; dt = t[1]-t[0] if len(t)>1 else 1e-6
        env1 = np.abs(hilbert(tx_v)); env2 = np.abs(hilbert(mic_v))
        noise_rms, ns, ne = self._auto_noise_rms(mic_v, env2, pre_list)
        self._last_noise_rms = noise_rms; self._last_noise_range = (ns, ne)
        
        # Calculate SNR accounting for system noise if calibration is high
        sig_std = np.std(mic_v)
        snr_db = 20*np.log10(sig_std / noise_rms) if noise_rms > 0 else 0
        
        self.noise_info_lbl.configure(text=f"σ: {noise_rms:.6f} V [{'manual' if self._noise_override else 'auto'}]")
        self.snr_lbl.configure(text=f"{snr_db:.1f} dB SNR"); self.dash_snr.configure(text=f"{snr_db:.1f} dB SNR")
        
        if getattr(self, '_last_burst_kwargs', None):
            kwargs = self._last_burst_kwargs.copy()
            kwargs.update({'noise_rms': noise_rms, 'ns': ns, 'ne': ne})
            self.update_burst_ui(**kwargs)
            
        self._is_dirty = True

    def _calculate_thd(self, fft_freqs, fft_mag, fundamental_hz, n_harmonics=5):
        if fundamental_hz <= 0 or len(fft_freqs) < 2: return 0.0, []
        df = fft_freqs[1] - fft_freqs[0]; search_width = max(1, int(200 / df))
        harmonic_mags = []
        for n in range(1, n_harmonics + 2):
            target_idx = int((fundamental_hz * n) / df)
            if target_idx >= len(fft_mag): break
            lo, hi = max(0, target_idx - search_width), min(len(fft_mag), target_idx + search_width)
            harmonic_mags.append(np.max(fft_mag[lo:hi]))
        if len(harmonic_mags) < 2 or harmonic_mags[0] < 1e-12: return 0.0, harmonic_mags
        fundamental = harmonic_mags[0]; harmonics_rss = np.sqrt(sum(h**2 for h in harmonic_mags[1:]))
        return (harmonics_rss / fundamental) * 100.0, harmonic_mags

    def _calculate_ringdown(self, env, dt, drop_db=20):
        peak_idx = np.argmax(env); peak_val = env[peak_idx]
        if peak_val < 1e-12: return None, peak_idx, peak_idx
        threshold = peak_val * 10 ** (-drop_db / 20.0)
        end_idx = peak_idx
        for i in range(peak_idx, len(env)):
            if env[i] < threshold:
                end_idx = i; break
        else: end_idx = len(env) - 1
        return (end_idx - peak_idx) * dt, peak_idx, end_idx

    # ------------------------------------------------------------------
    # UI Setup
    # ------------------------------------------------------------------
    def setup_ui(self):
        self.main_container = ctk.CTkFrame(self, fg_color="transparent"); self.main_container.pack(fill="both", expand=True)
        self.sidebar = ctk.CTkScrollableFrame(self.main_container, width=280); self.sidebar.pack(side="left", fill="y", padx=(8, 0), pady=8)
        self.tabs = ctk.CTkTabview(self.main_container); self.tabs.pack(side="right", fill="both", expand=True, padx=8, pady=8)
        self.tab_res   = self.tabs.add("Results Dashboard")
        self.tab_burst = self.tabs.add("Burst Analysis")
        self.tab_cwt   = self.tabs.add("Wavelet (CWT)")
        self.tab_adv   = self.tabs.add("STFT Spectrogram")
        self.tab_sweep = self.tabs.add("Resonance Sweep")
        self.tab_polar = self.tabs.add("Polar Plot")
        self.tab_imp   = self.tabs.add("Impedance")
        self._build_sidebar(self.sidebar)
        self.setup_results_tab(); self.setup_burst_tab(); self.setup_cwt_tab(); self.setup_adv_tab(); self.setup_sweep_tab(); self.setup_polar_tab(); self.setup_imp_tab()
        self.tabs.set("Burst Analysis")

    def _build_sidebar(self, p):
        make_label(p, "SYSTEM CONTROL", size=16, bold=True, color=("black", "white")).pack(pady=(2, 4))
        
        # Traffic Lights Hardware connection
        hw_f = ctk.CTkFrame(p, fg_color="#333333", corner_radius=8)
        hw_f.pack(fill="x", padx=10, pady=2)
        hw_f.grid_columnconfigure((0, 1, 2), weight=1)
        self.ind_fg  = ctk.CTkLabel(hw_f, text="⚫ FG", font=("Arial", 11, "bold"), text_color="gray")
        self.ind_scp = ctk.CTkLabel(hw_f, text="⚫ Scope", font=("Arial", 11, "bold"), text_color="gray")
        self.ind_mot = ctk.CTkLabel(hw_f, text="⚫ Motor", font=("Arial", 11, "bold"), text_color="gray")
        self.ind_fg.grid(row=0, column=0, pady=0)
        self.ind_scp.grid(row=0, column=1, pady=0)
        self.ind_mot.grid(row=0, column=2, pady=0)
        
        self.conn_btn = ctk.CTkButton(p, text="CONNECT HARDWARE", command=self.init_hw, fg_color="#1f538d", font=("Arial", 12, "bold"), height=28)
        self.conn_btn.pack(pady=2, padx=10, fill="x")

        make_label(p, "RX LEVEL / CLIPPING MONITOR", size=10, bold=True, color=("gray40", "gray70")).pack(pady=(4, 0))
        self.clip_bar = ctk.CTkProgressBar(p, progress_color="#4CAF50", height=10)
        self.clip_bar.set(0)
        self.clip_bar.pack(fill="x", padx=15, pady=2)
        
        self.auto_scale_btn = ctk.CTkButton(p, text="⚡ Smart Auto-Scale RX", command=self.smart_autoscale_rx, fg_color=("#f57f17", "#fbc02d"), text_color="black", font=("Arial", 11, "bold"), height=24)
        self.auto_scale_btn.pack(pady=(2, 6), padx=15, fill="x")

        # Removed the save/load buttons from the sidebar to keep UI clean
        self.stop_btn = ctk.CTkButton(p, text="🛑 STOP ALL", fg_color="#942121", font=("Arial", 11, "bold"), command=self.universal_stop, height=28)
        self.stop_btn.pack(fill="x", padx=10, pady=(4, 2))

        section_sep(p, "── CALIBRATION (RX) ──")
        
        # --- TIGHTENED UI SPACING (Left-Aligned to match Screenshot) ---
        cal_f = ctk.CTkFrame(p, fg_color="transparent")
        cal_f.pack(fill="x", padx=15) 
        cal_f.grid_columnconfigure((0, 1), weight=1)
        
        make_label(cal_f, "Temperature (°C)", size=11).grid(row=0, column=0, pady=(2, 0), sticky="w")
        make_label(cal_f, "Humidity (%RH)", size=11).grid(row=0, column=1, pady=(2, 0), sticky="w")
        
        self.temp_entry = ctk.CTkEntry(cal_f, width=100, height=26)
        self.temp_entry.insert(0, "22.0")
        self.temp_entry.grid(row=1, column=0, pady=(2, 8), sticky="w")
        
        self.humidity_entry = ctk.CTkEntry(cal_f, width=100, height=26)
        self.humidity_entry.insert(0, "50")
        self.humidity_entry.grid(row=1, column=1, pady=(2, 8), sticky="w")

        make_label(cal_f, "Mic Sens (mV/Pa)", size=11).grid(row=2, column=0, pady=0, sticky="w")
        make_label(cal_f, "Module Gain (dB)", size=11).grid(row=2, column=1, pady=0, sticky="w")
        
        self.mic_sens = ctk.CTkEntry(cal_f, width=100, height=26)
        self.mic_sens.insert(0, "0.9")
        self.mic_sens.grid(row=3, column=0, pady=(2, 0), sticky="w")
        
        self.module_gain = ctk.CTkEntry(cal_f, width=100, height=26)
        self.module_gain.insert(0, "50.0")
        self.module_gain.grid(row=3, column=1, pady=(2, 0), sticky="w")
        
        self.eff_sens_lbl = ctk.CTkLabel(p, text="", text_color=("gray60", "gray60"), font=("Arial", 11))
        self.eff_sens_lbl.pack(pady=(4, 6))
        
        self._update_eff_sens_label()
        self.mic_sens.bind("<KeyRelease>", lambda e: self._update_eff_sens_label())
        self.module_gain.bind("<KeyRelease>", lambda e: self._update_eff_sens_label())

        section_sep(p, "── MOTOR ALIGNMENT ──")
        m_f = ctk.CTkFrame(p, fg_color="transparent")
        m_f.pack(fill="x", padx=10)
        m_f.grid_columnconfigure((0, 1), weight=1)
        ctk.CTkButton(m_f, text="◀ STEP L", width=80, height=26, command=lambda: self.jog_motor(-1)).grid(row=0, column=0, padx=5, pady=2)
        ctk.CTkButton(m_f, text="STEP R ▶", width=80, height=26, command=lambda: self.jog_motor(1)).grid(row=0, column=1, padx=5, pady=2)
        ctk.CTkButton(p, text="SET 0° CENTER", fg_color="#D4AF37", text_color="black", font=("Arial", 11, "bold"), height=26, command=self.set_new_center).pack(pady=2, padx=15, fill="x")

        section_sep(p, "── REFERENCE DISTANCE ──")
        
        dist_f = ctk.CTkFrame(p, fg_color="transparent")
        dist_f.pack(fill="x", padx=15)
        dist_f.grid_columnconfigure((0, 1), weight=1)
        
        make_label(dist_f, "Distance (cm)", size=11).grid(row=0, column=0, pady=(2, 0), sticky="w")
        
        self.ref_dist_entry = ctk.CTkEntry(dist_f, width=100, height=26)
        self.ref_dist_entry.insert(0, "30.0")
        self.ref_dist_entry.grid(row=1, column=0, pady=(2, 0), sticky="w")
        
        self.ref_dist_lock_var = ctk.StringVar(value="off")
        ctk.CTkCheckBox(dist_f, text="Override ToF", variable=self.ref_dist_lock_var, onvalue="on", offvalue="off", font=("Arial", 11)).grid(row=1, column=1, pady=(2, 0), sticky="w")
        
        ctk.CTkLabel(p, text="Override = Force calcs (e.g., Source Level) to use\nthis manual distance instead of Time-of-Flight", font=("Arial", 10), text_color=("gray50", "gray60"), justify="left").pack(padx=15, pady=(4, 0), anchor="w")

        section_sep(p, "── LOG ──")
        self.log_box = ctk.CTkTextbox(p, height=75)
        self.log_box.pack(pady=(2, 6), padx=8, fill="x")

    def setup_results_tab(self):
        self.tab_res.grid_columnconfigure((0, 1), weight=1)
        self.tab_res.grid_rowconfigure((0, 1), weight=1)

        def add_card(parent, row, col, label_text, val_text, val_color, val_size=24):
            card = ctk.CTkFrame(parent, fg_color=("#d6d6d6", "#333333"), corner_radius=10); card.grid(row=row, column=col, padx=8, pady=8, sticky="nsew")
            lbl_val = ctk.CTkLabel(card, text=val_text, font=("Arial", val_size, "bold"), text_color=val_color); lbl_val.pack(expand=True, side="bottom", pady=(0, 15))
            make_label(card, label_text, size=12, color=("gray40","gray70"), bold=True).pack(expand=True, side="top", pady=(15, 0))
            return lbl_val

        f_burst = ctk.CTkFrame(self.tab_res, fg_color=("#e0e0e0", "#2b2b2b"), corner_radius=15); f_burst.grid(row=0, column=0, columnspan=2, padx=10, pady=(10, 5), sticky="nsew")
        make_label(f_burst, "BURST METRICS", size=18, bold=True, color=("#e65100", "orange")).pack(pady=(15, 5))
        b_grid = ctk.CTkFrame(f_burst, fg_color="transparent"); b_grid.pack(expand=True, fill="both", padx=10, pady=5)
        b_grid.grid_columnconfigure((0, 1, 2, 3), weight=1); b_grid.grid_rowconfigure((0, 1), weight=1)

        self.dash_vpp  = add_card(b_grid, 0, 0, "Scope Vpp", "-- V", ("#00c853","#00E676"))
        self.dash_pa   = add_card(b_grid, 0, 1, "Acoustic Pressure", "-- Pa", ("#0277bd","#00B0FF"))
        self.dash_spl  = add_card(b_grid, 0, 2, "Peak SPL (RMS)", "-- dB SPL", ("#d84315","#FF3D00"))
        self.dash_sl   = add_card(b_grid, 0, 3, "Source Level @ 1m", "SL@1m: --", ("#6a1b9a","#ce93d8"))
        self.dash_snr  = add_card(b_grid, 1, 0, "Signal/Noise Ratio", "-- dB SNR", ("#fbc02d","#FFEA00"))
        self.dash_dist = add_card(b_grid, 1, 1, "Time-of-Flight Dist", "-- cm", ("#8e24aa","#E040FB"))
        self.dash_thd  = add_card(b_grid, 1, 2, "Harmonic Distortion", "THD: --%", ("gray40","gray70"))
        self.dash_tau  = add_card(b_grid, 1, 3, "Ring-Down (-20dB)", "τ₂₀: -- ms", ("#00695c","#4db6ac"))

        f_sweep = ctk.CTkFrame(self.tab_res, fg_color=("#e0e0e0", "#2b2b2b"), corner_radius=15); f_sweep.grid(row=1, column=0, padx=(10, 5), pady=(5, 10), sticky="nsew")
        make_label(f_sweep, "RESONANCE METRICS", size=18, bold=True, color=("#0288d1","#4fc3f7")).pack(pady=(15, 5))
        s_grid = ctk.CTkFrame(f_sweep, fg_color="transparent"); s_grid.pack(expand=True, fill="both", padx=10, pady=5)
        s_grid.grid_columnconfigure((0, 1, 2), weight=1); s_grid.grid_rowconfigure(0, weight=1)

        self.dash_peak_f = add_card(s_grid, 0, 0, "Peak Frequency", "-- kHz", ("#fbc02d","#FFEA00"))
        card_bw = ctk.CTkFrame(s_grid, fg_color=("#d6d6d6", "#333333"), corner_radius=10); card_bw.grid(row=0, column=1, padx=8, pady=8, sticky="nsew")
        self.dash_bw = ctk.CTkLabel(card_bw, text="-- kHz", font=("Arial", 24, "bold"), text_color=("#0277bd","#00B0FF")); self.dash_bw.pack(expand=True, side="bottom", pady=(0, 15))
        self.dash_bw_title = make_label(card_bw, "Bandwidth (-6dB)", size=12, color=("gray40","gray70"), bold=True); self.dash_bw_title.pack(expand=True, side="top", pady=(15, 0))
        self.dash_q = add_card(s_grid, 0, 2, "Quality Factor (Q)", "--", ("#00c853","#00E676"))

        f_polar = ctk.CTkFrame(self.tab_res, fg_color=("#e0e0e0", "#2b2b2b"), corner_radius=15); f_polar.grid(row=1, column=1, padx=(5, 10), pady=(5, 10), sticky="nsew")
        make_label(f_polar, "DIRECTIONAL METRICS", size=18, bold=True, color=("#388e3c","#a5d6a7")).pack(pady=(15, 5))
        p_grid = ctk.CTkFrame(f_polar, fg_color="transparent"); p_grid.pack(expand=True, fill="both", padx=10, pady=5)
        p_grid.grid_columnconfigure((0, 1), weight=1); p_grid.grid_rowconfigure(0, weight=1)

        self.dash_bw3 = add_card(p_grid, 0, 0, "-3dB Beamwidth", "-- °", ("#d84315","#FF3D00"))
        self.dash_bw6 = add_card(p_grid, 0, 1, "-6dB Beamwidth", "-- °", ("#fbc02d","#FFEA00"))

    def setup_burst_tab(self):
        pw = tk.PanedWindow(self.tab_burst, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left_container = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left_container, minsize=250); self._tk_frames.append(left_container)
        self.ctrl_burst = ctk.CTkScrollableFrame(left_container, width=320); self.ctrl_burst.pack(fill="both", expand=True)
        plot_frame = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(plot_frame, minsize=400)

        make_label(self.ctrl_burst, "BURST ANALYSIS", size=13, bold=True, color=("#e65100", "orange")).pack(pady=(8, 4))
        self.btn_run_burst = ctk.CTkButton(self.ctrl_burst, text="▶  RUN", fg_color=("#2e7d32", "green"), font=("Arial", 13, "bold"), command=self.start_burst_thread); self.btn_run_burst.pack(pady=(0, 4), padx=8, fill="x")
        self.burst_voltage, self.burst_cycles = drive_voltage_row(self.ctrl_burst)

        section_sep(self.ctrl_burst, "── FG Output Mode ──")
        self.burst_fg_mode = ctk.CTkSegmentedButton(self.ctrl_burst, values=["Burst", "Continuous", "Modulation"], command=self._on_fg_mode_change)
        self.burst_fg_mode.set("Burst"); self.burst_fg_mode.pack(pady=3, padx=5, fill="x")
        self.tof_note = ctk.CTkLabel(self.ctrl_burst, text="✓ ToF distance active", font=("Arial", 10), text_color=("#2e7d32", "#4caf50")); self.tof_note.pack(pady=(0, 4))

        section_sep(self.ctrl_burst, "── Signal ──")
        self.burst_f = labeled_entry(self.ctrl_burst, "Frequency (kHz)", "")
        self.burst_wave = labeled_seg(self.ctrl_burst, "Waveform Type", ["Sine", "Square", "Triangle", "Ramp"], "Sine", command=self._on_burst_wave_change)

        self.panel_burst = ctk.CTkFrame(self.ctrl_burst, fg_color="transparent"); section_sep(self.panel_burst, "── Burst Settings ──")
        self.burst_capture_time = labeled_entry(self.panel_burst, "FG On Duration (s)", "1.2"); self.burst_dwell = labeled_entry(self.panel_burst, "Dwell After Burst (s)", "0.5")
        self.panel_cont = ctk.CTkFrame(self.ctrl_burst, fg_color="transparent"); section_sep(self.panel_cont, "── Continuous Settings ──")
        self.panel_mod = ctk.CTkFrame(self.ctrl_burst, fg_color="transparent"); section_sep(self.panel_mod, "── Modulation Settings ──")
        self.mod_type   = labeled_seg(self.panel_mod, "Mod Type", ["AM", "FM", "PM", "FSK"], "AM")
        self.mod_freq   = labeled_entry(self.panel_mod, "Mod Frequency (Hz)", "1000")
        self.mod_depth  = labeled_entry(self.panel_mod, "AM Depth (%) / FM Dev (Hz)", "50")
        self.mod_wave   = labeled_seg(self.panel_mod, "Mod Waveform", ["Sine", "Square", "Ramp"], "Sine")
        self.mod_source = labeled_seg(self.panel_mod, "Mod Source", ["Internal", "External"], "Internal")
        self.panel_burst.pack(fill="x")

        section_sep(self.ctrl_burst, "── Scope (Fixed CH1/CH2) ──")
        self.burst_acq   = labeled_seg(self.ctrl_burst, "Acquire Mode", ["Normal", "Average", "Peak"], "Average")
        self.burst_avg_n = labeled_entry(self.ctrl_burst, "Averages", "32")
        self.burst_settle = labeled_entry(self.ctrl_burst, "Pre-Trig Settle (s)", "0.1")
        
        make_label(self.ctrl_burst, "↕️ TX/RX Vertical Spacing").pack(pady=(4, 0))
        self.burst_sep_slider = ctk.CTkSlider(self.ctrl_burst, from_=1.0, to=30.0, command=self._update_burst_separation)
        self.burst_sep_slider.set(4.0)
        self.burst_sep_slider.pack(fill="x", padx=15, pady=(0, 6))

        section_sep(self.ctrl_burst, "── FFT Plot Range ──")
        self.fft_fmin, self.fft_fmax = two_column_entries(self.ctrl_burst, "Min Freq (kHz)", "Max Freq (kHz)")

        section_sep(self.ctrl_burst, "── Ring-Down View ──")
        self.ringdown_ext = labeled_entry(self.ctrl_burst, "Extra Tail (ms)", "0.0")
        ctk.CTkLabel(self.ctrl_burst, text="Extend plot right to see\nmore of the ring-down tail", font=("Arial", 9), text_color=("gray50","gray60"), justify="left").pack(padx=15, anchor="w")

        section_sep(self.ctrl_burst, "── Noise Floor ──")
        self.noise_info_lbl = ctk.CTkLabel(self.ctrl_burst, text="σ: auto", font=("Arial", 10), text_color=("gray40", "gray70")); self.noise_info_lbl.pack(pady=(2, 2))
        ctk.CTkButton(self.ctrl_burst, text="🔍 Adjust Noise Floor", fg_color=("#455a64", "#607d8b"), font=("Arial", 11), command=self._open_noise_selector).pack(pady=(0, 4), padx=8, fill="x")
        ctk.CTkButton(self.ctrl_burst, text="🛡️ Noise Calibration", fg_color=("#0288d1", "#0277bd"), font=("Arial", 11, "bold"), command=self._open_noise_calibration).pack(pady=(0, 6), padx=8, fill="x")

        section_sep(self.ctrl_burst, "── RESULTS ──")
        self.vpp_scope_lbl = ctk.CTkLabel(self.ctrl_burst, text="Scope:  -- V",  font=("Arial", 16, "bold"), text_color=("#00c853","#00E676")); self.vpp_scope_lbl.pack(pady=2)
        self.vpp_pa_lbl    = ctk.CTkLabel(self.ctrl_burst, text="Acoustic: -- Pa",font=("Arial", 16, "bold"), text_color=("#0277bd","#00B0FF")); self.vpp_pa_lbl.pack(pady=2)
        self.snr_lbl       = ctk.CTkLabel(self.ctrl_burst, text="-- dB SNR",     font=("Arial", 18, "bold"), text_color=("#fbc02d","#FFEA00")); self.snr_lbl.pack(pady=4)
        self.spl_lbl       = ctk.CTkLabel(self.ctrl_burst, text="-- dB SPL",     font=("Arial", 18, "bold"), text_color=("#d84315","#FF3D00")); self.spl_lbl.pack(pady=4)
        self.sl_lbl        = ctk.CTkLabel(self.ctrl_burst, text="SL@1m: --",     font=("Arial", 16, "bold"), text_color=("#6a1b9a","#ce93d8")); self.sl_lbl.pack(pady=2)
        self.dist_lbl      = ctk.CTkLabel(self.ctrl_burst, text="-- cm",         font=("Arial", 26, "bold"), text_color=("#8e24aa","#E040FB")); self.dist_lbl.pack(pady=6)
        self.thd_lbl       = ctk.CTkLabel(self.ctrl_burst, text="THD: --%",      font=("Arial", 16, "bold"), text_color=("gray40","gray70")); self.thd_lbl.pack(pady=2)
        self.thd_warn_lbl  = ctk.CTkLabel(self.ctrl_burst, text="",              font=("Arial", 11, "bold"), text_color=("#c62828","#ff5252")); self.thd_warn_lbl.pack(pady=0)
        self.tau_lbl       = ctk.CTkLabel(self.ctrl_burst, text="τ₂₀: -- ms",    font=("Arial", 16, "bold"), text_color=("#00695c","#4db6ac")); self.tau_lbl.pack(pady=2)
        section_sep(self.ctrl_burst)

        self.fig_b = plt.figure(figsize=(10, 8), facecolor="white")
        self.canvas_b = FigureCanvasTkAgg(self.fig_b, master=plot_frame)
        self.canvas_b.mpl_connect('pick_event', self._on_legend_pick)
        self.canvas_b.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock the toolbar frame height to 40 pixels so coordinate updates don't cause app flickering
        tbf = tk.Frame(plot_frame, bg="#333333", height=40); tbf.pack_propagate(False); tbf.pack(side="top", fill="x")
        
        self.toolbar_b = NavigationToolbar2Tk(self.canvas_b, tbf); self.toolbar_b.update()
        self._bind_custom_home(self.toolbar_b, self.fig_b)
        
        # FIX: Pack the button directly into the Matplotlib toolbar so it doesn't get clipped!
        self._add_fullscreen_btn(self.toolbar_b, self.fig_b, "Burst Analysis")
        ctk.CTkLabel(plot_frame, text="💡 Tip: Double-click plot to add coordinate markers. Click legends/titles to edit. Click 'Home' 🏠 to reset.", font=("Arial", 11), text_color=("gray50", "gray60")).pack(side="bottom", pady=2)
        self.canvas_b.get_tk_widget().pack(side="top", fill="both", expand=True)

    def _on_fg_mode_change(self, mode):
        for panel in [self.panel_burst, self.panel_cont, self.panel_mod]: panel.pack_forget()
        if mode == "Burst": self.panel_burst.pack(fill="x")
        elif mode == "Continuous": self.panel_cont.pack(fill="x")
        elif mode == "Modulation": self.panel_mod.pack(fill="x")
    def _on_burst_wave_change(self, selected): pass

    def setup_cwt_tab(self):
        pw = tk.PanedWindow(self.tab_cwt, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left, minsize=250); self._tk_frames.append(left)
        self.ctrl_cwt = ctk.CTkScrollableFrame(left, width=320); self.ctrl_cwt.pack(fill="both", expand=True)
        pf = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(pf, minsize=400)
        make_label(self.ctrl_cwt, "WAVELET ANALYSIS", size=13, bold=True, color=("#6a1b9a","#e040fb")).pack(pady=(8, 4))
        self.btn_run_cwt = ctk.CTkButton(self.ctrl_cwt, text="▶  RUN CWT", fg_color=("#2e7d32","green"), font=("Arial", 13, "bold"), command=self.start_cwt_thread); self.btn_run_cwt.pack(pady=(0,4), padx=8, fill="x")
        self.cwt_voltage, self.cwt_cycles = drive_voltage_row(self.ctrl_cwt)
        self.cwt_wave = labeled_seg(self.ctrl_cwt, "Waveform Type", ["Sine", "Square", "Triangle", "Ramp"], "Square")
        section_sep(self.ctrl_cwt, "── Drive Signal ──"); self.cwt_f = labeled_entry(self.ctrl_cwt, "Center Freq (kHz)", "")
        
        section_sep(self.ctrl_cwt, "── Scope Settings (RX) ──")
        self.cwt_acq   = labeled_seg(self.ctrl_cwt, "Acquire Mode", ["Normal", "Average", "Peak"], "Average")
        self.cwt_avg_n = labeled_entry(self.ctrl_cwt, "Averages", "128")
        self.cwt_settle = labeled_entry(self.ctrl_cwt, "Pre-Trig Settle (s)", "0.5")

        section_sep(self.ctrl_cwt, "── Plot Boundaries ──"); self.cwt_fmin, self.cwt_fmax = two_column_entries(self.ctrl_cwt, "Min Freq (kHz)", "Max Freq (kHz)")
        section_sep(self.ctrl_cwt, "── Time Window ──"); self.cwt_pre, self.cwt_tail = two_column_entries(self.ctrl_cwt, "Pre-Peak (ms)", "Tail (ms)", "0.3", "1.0")
        self.fig_cwt = plt.figure(figsize=(11, 4), facecolor="white"); self.ax_cwt = self.fig_cwt.add_subplot(111)
        self.canvas_cwt = FigureCanvasTkAgg(self.fig_cwt, master=pf); self.canvas_cwt.mpl_connect('pick_event', self._on_legend_pick); self.canvas_cwt.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock toolbar height
        tf = tk.Frame(pf, bg="#333333", height=40); tf.pack_propagate(False); tf.pack(side="top", fill="x")
        
        self.toolbar_cwt = NavigationToolbar2Tk(self.canvas_cwt, tf); self.toolbar_cwt.update(); self._bind_custom_home(self.toolbar_cwt, self.fig_cwt)
        
        # FIX: Pack into the toolbar
        self._add_fullscreen_btn(self.toolbar_cwt, self.fig_cwt, "Wavelet (CWT)")
        ctk.CTkLabel(pf, text="💡 Tip: Double-click plot to add coordinate markers. Click legends/titles to edit. Click 'Home' 🏠 to reset.", font=("Arial", 11), text_color=("gray50", "gray60")).pack(side="bottom", pady=2)
        self.canvas_cwt.get_tk_widget().pack(side="top", fill="both", expand=True)

    def setup_adv_tab(self):
        pw = tk.PanedWindow(self.tab_adv, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left, minsize=250); self._tk_frames.append(left)
        self.ctrl_adv = ctk.CTkScrollableFrame(left, width=320); self.ctrl_adv.pack(fill="both", expand=True)
        pf = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(pf, minsize=400)
        make_label(self.ctrl_adv, "STFT SPECTROGRAM", size=13, bold=True, color=("#c62828","#ff5252")).pack(pady=(8, 4))
        self.btn_run_adv = ctk.CTkButton(self.ctrl_adv, text="▶  RUN STFT", fg_color=("#2e7d32","green"), font=("Arial", 13, "bold"), command=self.start_adv_thread); self.btn_run_adv.pack(pady=(0,4), padx=8, fill="x")
        self.adv_voltage, self.adv_cycles = drive_voltage_row(self.ctrl_adv)
        self.adv_wave = labeled_seg(self.ctrl_adv, "Waveform Type", ["Sine", "Square", "Triangle", "Ramp"], "Square")
        section_sep(self.ctrl_adv, "── Drive Signal ──"); self.adv_f = labeled_entry(self.ctrl_adv, "Center Freq (kHz)", "")
        
        section_sep(self.ctrl_adv, "── Scope Settings (RX) ──")
        self.adv_acq   = labeled_seg(self.ctrl_adv, "Acquire Mode", ["Normal", "Average", "Peak"], "Average")
        self.adv_avg_n = labeled_entry(self.ctrl_adv, "Averages", "128")
        self.adv_settle = labeled_entry(self.ctrl_adv, "Pre-Trig Settle (s)", "0.5")

        section_sep(self.ctrl_adv, "── Plot Boundaries ──"); self.adv_fmin, self.adv_fmax = two_column_entries(self.ctrl_adv, "Min Freq (kHz)", "Max Freq (kHz)")
        section_sep(self.ctrl_adv, "── Time Window ──"); self.adv_pre, self.adv_tail = two_column_entries(self.ctrl_adv, "Pre-Peak (ms)", "Tail (ms)", "0.3", "1.0")
        self.fig_adv = plt.figure(figsize=(11, 4), facecolor="white"); self.ax_adv = self.fig_adv.add_subplot(111)
        self.canvas_adv = FigureCanvasTkAgg(self.fig_adv, master=pf); self.canvas_adv.mpl_connect('pick_event', self._on_legend_pick); self.canvas_adv.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock toolbar height
        tf = tk.Frame(pf, bg="#333333", height=40); tf.pack_propagate(False); tf.pack(side="top", fill="x")
        
        self.toolbar_adv = NavigationToolbar2Tk(self.canvas_adv, tf); self.toolbar_adv.update(); self._bind_custom_home(self.toolbar_adv, self.fig_adv)
        
        # FIX: Pack into the toolbar
        self._add_fullscreen_btn(self.toolbar_adv, self.fig_adv, "STFT Spectrogram")
        ctk.CTkLabel(pf, text="💡 Tip: Double-click plot to add coordinate markers. Click legends/titles to edit. Click 'Home' 🏠 to reset.", font=("Arial", 11), text_color=("gray50", "gray60")).pack(side="bottom", pady=2)
        self.canvas_adv.get_tk_widget().pack(side="top", fill="both", expand=True)

    def setup_sweep_tab(self):
        pw = tk.PanedWindow(self.tab_sweep, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left, minsize=250); self._tk_frames.append(left)
        self.ctrl_sweep = ctk.CTkScrollableFrame(left, width=320); self.ctrl_sweep.pack(fill="both", expand=True)
        pf = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(pf, minsize=400)
        make_label(self.ctrl_sweep, "SWEEP SETTINGS", size=13, bold=True, color=("#0288d1","#4fc3f7")).pack(pady=(8, 4))
        self.btn_run_sweep = ctk.CTkButton(self.ctrl_sweep, text="▶  START SWEEP", fg_color=("#2e7d32","green"), font=("Arial", 13, "bold"), command=self.start_sweep_thread); self.btn_run_sweep.pack(pady=(0,4), padx=8, fill="x")
        self.sweep_progress = ctk.CTkProgressBar(self.ctrl_sweep, height=10); self.sweep_progress.set(0); self.sweep_progress.pack(pady=(2,0), padx=10, fill="x")
        self.sweep_prog_lbl = ctk.CTkLabel(self.ctrl_sweep, text="Ready", font=("Arial", 10), text_color=("gray40","gray70")); self.sweep_prog_lbl.pack(pady=(0,4))
        
        # FIX: Replaced the side-by-side Burst row with a single Continuous voltage entry
        self.sweep_voltage = labeled_entry(self.ctrl_sweep, "Drive Voltage (V)", "5")

        section_sep(self.ctrl_sweep, "── Frequency Range ──")
        self.start_f, self.end_f = two_column_entries(self.ctrl_sweep, "Start (kHz)", "End (kHz)")
        self.step_f = labeled_entry(self.ctrl_sweep, "Step (kHz)", "0.1")
        self.sweep_spacing = labeled_seg(self.ctrl_sweep, "Frequency Spacing", ["Linear", "Log"], "Linear")
        section_sep(self.ctrl_sweep, "── Waveform ──"); self.sweep_wave = labeled_seg(self.ctrl_sweep, "Waveform Type", ["Sine", "Square", "Triangle", "Ramp"], "Sine")
        section_sep(self.ctrl_sweep, "── Scope (RX: CH2) ──")
        self.sweep_meas  = labeled_seg(self.ctrl_sweep, "Measurement", ["RMS", "Peak", "Vpp"], "RMS")
        self.sweep_dwell = labeled_entry(self.ctrl_sweep, "Dwell Time (s)", "0.3")
        section_sep(self.ctrl_sweep, "── Display ──"); self.sweep_yaxis = labeled_seg(self.ctrl_sweep, "Y Axis", ["SPL (dB)", "Pa RMS", "V RMS"], "SPL (dB)")
        section_sep(self.ctrl_sweep, "── Bandwidth Thresholds ──"); self.bw_thresh_seg = labeled_seg(self.ctrl_sweep, "Show BW at", ["-3 dB", "-6 dB", "-10 dB", "-20 dB"], "-6 dB")
        ctk.CTkLabel(self.ctrl_sweep, text="The selected threshold will be shown\non the Results Dashboard.", font=("Arial", 9), text_color=("gray50","gray60"), justify="left").pack(padx=15, anchor="w")

        section_sep(self.ctrl_sweep, "── RESULTS ──")
        self.peak_f_lbl = ctk.CTkLabel(self.ctrl_sweep, text="Peak: -- kHz", font=("Arial", 22, "bold"), text_color=("#fbc02d","#FFEA00")); self.peak_f_lbl.pack(pady=3)
        self.q_lbl      = ctk.CTkLabel(self.ctrl_sweep, text="Q: --",        font=("Arial", 18, "bold"), text_color=("#00c853","#00E676")); self.q_lbl.pack(pady=3)
        self.bw_labels = {}
        bw_colors = {"3.0": ("#d84315","#FF3D00"), "6.0": ("#e65100","#FF6D00"), "10.0": ("#f9a825","#FFD600"), "20.0": ("#757575","#BDBDBD")}
        for key, db in BW_THRESHOLDS.items():
            col = bw_colors.get(str(db), ("gray","gray"))
            lbl = ctk.CTkLabel(self.ctrl_sweep, text=f"{key}: -- kHz", font=("Arial", 14, "bold"), text_color=col); lbl.pack(pady=1)
            self.bw_labels[db] = lbl
        self.bw_lbl = self.bw_labels[3.0]; section_sep(self.ctrl_sweep)

        self.fig_sw = plt.figure(facecolor="white")
        gs = self.fig_sw.add_gridspec(1, 3, width_ratios=[3, 2, 1.5])
        self.ax_sw = self.fig_sw.add_subplot(gs[0]); self.ax_bw = self.fig_sw.add_subplot(gs[1]); self.ax_qgauge = self.fig_sw.add_subplot(gs[2])
        for ax in [self.ax_bw, self.ax_qgauge]: ax.set_xticks([]); ax.set_yticks([]); ax.set_title("Waiting...", fontsize=10, color="gray")
        self.canvas_sw = FigureCanvasTkAgg(self.fig_sw, master=pf); self.canvas_sw.mpl_connect('pick_event', self._on_legend_pick); self.canvas_sw.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock toolbar height
        tf = tk.Frame(pf, bg="#333333", height=40); tf.pack_propagate(False); tf.pack(side="top", fill="x")
        
        self.toolbar_sw = NavigationToolbar2Tk(self.canvas_sw, tf); self.toolbar_sw.update(); self._bind_custom_home(self.toolbar_sw, self.fig_sw)
        
        # FIX: Pack into the toolbar
        self._add_fullscreen_btn(self.toolbar_sw, self.fig_sw, "Resonance Sweep")
        ctk.CTkLabel(pf, text="💡 Tip: Double-click plot to add coordinate markers. Click legends/titles to edit. Click 'Home' 🏠 to reset.", font=("Arial", 11), text_color=("gray50", "gray60")).pack(side="bottom", pady=2)
        self.canvas_sw.get_tk_widget().pack(side="top", fill="both", expand=True)

    def setup_polar_tab(self):
        pw = tk.PanedWindow(self.tab_polar, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left, minsize=250); self._tk_frames.append(left)
        self.ctrl_polar = ctk.CTkScrollableFrame(left, width=320); self.ctrl_polar.pack(fill="both", expand=True)
        pf = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(pf, minsize=400)
        make_label(self.ctrl_polar, "POLAR SETTINGS", size=13, bold=True, color=("#388e3c","#a5d6a7")).pack(pady=(8, 4))
        self.btn_run_polar = ctk.CTkButton(self.ctrl_polar, text="▶  START SCAN", fg_color=("#2e7d32","green"), font=("Arial", 13, "bold"), command=self.start_polar_thread); self.btn_run_polar.pack(pady=(0,3), padx=8, fill="x")
        self.polar_progress = ctk.CTkProgressBar(self.ctrl_polar, height=10); self.polar_progress.set(0); self.polar_progress.pack(pady=(2,0), padx=10, fill="x")
        self.polar_prog_lbl = ctk.CTkLabel(self.ctrl_polar, text="Ready", font=("Arial", 10), text_color=("gray40","gray70")); self.polar_prog_lbl.pack(pady=(0,4))
        ctk.CTkButton(self.ctrl_polar, text="Clear Plot", fg_color=("#b0bec5","#555"), text_color=("black","white"), command=self._clear_polar).pack(pady=(0,6), padx=8, fill="x")
        
        # FIX: Replaced the side-by-side Burst row with a single Continuous voltage entry
        self.polar_voltage = labeled_entry(self.ctrl_polar, "Drive Voltage (V)", "5")
        
        section_sep(self.ctrl_polar, "── Signal ──"); self.pol_f = labeled_entry(self.ctrl_polar, "Frequency (kHz)", "")
        self.polar_wave = labeled_seg(self.ctrl_polar, "Waveform Type", ["Sine", "Square", "Triangle", "Ramp"], "Sine")
        section_sep(self.ctrl_polar, "── Angle Range ──"); self.pol_start, self.pol_end = two_column_entries(self.ctrl_polar, "Start (°)", "End (°)", "-90", "90")
        self.pol_step = labeled_entry(self.ctrl_polar, "Step Size (°)", "5")
        self.pol_dir = labeled_seg(self.ctrl_polar, "Scan Direction", ["Start→End", "End→Start", "Both"], "Start→End")
        section_sep(self.ctrl_polar, "── Scope (RX: CH2) ──"); self.pol_dwell = labeled_entry(self.ctrl_polar, "Dwell per Step (s)", "1.2")
        self.pol_range   = labeled_seg(self.ctrl_polar, "Plot Range (dB)", ["-20", "-30", "-40", "-60"], "-30")
        self.pol_overlay = labeled_seg(self.ctrl_polar, "Overlay Mode", ["Replace", "Overlay"], "Replace")
        
        section_sep(self.ctrl_polar, "── Theoretical Prediction ──")
        self.pred_geom = labeled_seg(self.ctrl_polar, "Geometry", ["Circular", "Rectangular"], "Circular", command=lambda _: self.update_polar_prediction())
        self.pred_dim = labeled_entry(self.ctrl_polar, "Dimension (Diameter/Width) mm", "10.0")
        self.pred_dim.bind("<KeyRelease>", lambda e: self.update_polar_prediction())
        
        mode_f = ctk.CTkFrame(self.ctrl_polar, fg_color="transparent")
        mode_f.pack(fill="x", padx=5)
        mode_f.grid_columnconfigure((0, 1), weight=1)
        make_label(mode_f, "Mode n (Radial)").grid(row=0, column=0)
        make_label(mode_f, "Mode m (Angular)").grid(row=0, column=1)
        self.pred_mode_n = ctk.CTkEntry(mode_f, width=100); self.pred_mode_n.insert(0, "0")
        self.pred_mode_n.bind("<KeyRelease>", lambda e: self.update_polar_prediction())
        self.pred_mode_n.grid(row=1, column=0, padx=5, pady=3)
        self.pred_mode_m = ctk.CTkEntry(mode_f, width=100); self.pred_mode_m.insert(0, "0")
        self.pred_mode_m.bind("<KeyRelease>", lambda e: self.update_polar_prediction())
        self.pred_mode_m.grid(row=1, column=1, padx=5, pady=3)
        
        ctk.CTkLabel(self.ctrl_polar, text="Note: n=0, m=0 is the fundamental clamped mode.", font=("Arial", 10), text_color=("gray50", "gray60")).pack(anchor="w", padx=15, pady=(0, 4))
        
        self.pred_show = ctk.CTkCheckBox(self.ctrl_polar, text="Show Theoretical Pattern", font=("Arial", 11), command=self.update_polar_prediction)
        self.pred_show.pack(pady=5, padx=10, anchor="w")
        
        section_sep(self.ctrl_polar, "── RESULTS ──")
        self.pol_bw3_lbl = ctk.CTkLabel(self.ctrl_polar, text="-3dB: -- °", font=("Arial", 22, "bold"), text_color=("#d84315","#FF3D00")); self.pol_bw3_lbl.pack(pady=4)
        self.pol_bw6_lbl = ctk.CTkLabel(self.ctrl_polar, text="-6dB: -- °", font=("Arial", 22, "bold"), text_color=("#fbc02d","#FFEA00")); self.pol_bw6_lbl.pack(pady=4)
        section_sep(self.ctrl_polar)
        self.fig_p = plt.figure(figsize=(7, 7), facecolor="white"); self.ax_p = self.fig_p.add_subplot(111, projection='polar')
        self.ax_p.set_theta_zero_location("N"); self.ax_p.set_theta_direction(-1)
        self.canvas_p = FigureCanvasTkAgg(self.fig_p, master=pf); self.canvas_p.mpl_connect('pick_event', self._on_legend_pick); self.canvas_p.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock toolbar height
        tf = tk.Frame(pf, bg="#333333", height=40); tf.pack_propagate(False); tf.pack(side="top", fill="x")
        
        self.toolbar_p = NavigationToolbar2Tk(self.canvas_p, tf); self.toolbar_p.update(); self._bind_custom_home(self.toolbar_p, self.fig_p)
        
        # FIX: Pack into the toolbar
        self._add_fullscreen_btn(self.toolbar_p, self.fig_p, "Polar Plot")
        self.canvas_p.get_tk_widget().pack(side="top", fill="both", expand=True)
        self._polar_overlays = []
        self._last_polar_al = None
        self._last_polar_vl = None

    def _clear_polar(self):
        # FIX: Also clear the underlying raw data array so it doesn't accidentally get exported later, and trip the dirty flag
        self.last_polar_data = None
        self._polar_overlays = []
        self._last_polar_al = None
        self._last_polar_vl = None
        self.ax_p.clear()
        self.ax_p.set_theta_zero_location("N")
        self.ax_p.set_theta_direction(-1)
        self.canvas_p.draw()
        self._is_dirty = True

    # ------------------------------------------------------------------
    # Impedance Analyzer
    # ------------------------------------------------------------------
    def setup_imp_tab(self):
        pw = tk.PanedWindow(self.tab_imp, orient=tk.HORIZONTAL, sashwidth=6, bg="#333333", bd=0, sashcursor="sb_h_double_arrow"); pw.pack(fill="both", expand=True); self._paned_windows.append(pw)
        left = tk.Frame(pw, bg="#242424", cursor="arrow"); pw.add(left, minsize=250); self._tk_frames.append(left)
        self.ctrl_imp = ctk.CTkScrollableFrame(left, width=320); self.ctrl_imp.pack(fill="both", expand=True)
        pf = ctk.CTkFrame(pw, fg_color="transparent", cursor="arrow"); pw.add(pf, minsize=400)
        make_label(self.ctrl_imp, "IMPEDANCE ANALYZER", size=13, bold=True, color=("#0288d1","#4fc3f7")).pack(pady=(8, 4))
        
        btn_f = ctk.CTkFrame(self.ctrl_imp, fg_color="transparent"); btn_f.pack(fill="x", padx=10, pady=5); btn_f.grid_columnconfigure((0,1), weight=1)
        ctk.CTkButton(btn_f, text="📂 IMPORT CSV", fg_color=("#2e7d32","green"), font=("Arial", 12, "bold"), command=self.import_imp_csv).grid(row=0, column=0, padx=2)
        ctk.CTkButton(btn_f, text="🗑️ CLEAR", fg_color="#942121", font=("Arial", 12, "bold"), command=self.clear_imp_data).grid(row=0, column=1, padx=2)
        
        section_sep(self.ctrl_imp, "── Plot Range ──")
        self.imp_fmin, self.imp_fmax = two_column_entries(self.ctrl_imp, "Min Freq (kHz)", "Max Freq (kHz)")
        ctk.CTkButton(self.ctrl_imp, text="Apply Range", fg_color=("#455a64", "#607d8b"), font=("Arial", 11), height=24, command=self.update_imp_plot).pack(pady=(0, 6), padx=8, fill="x")
        
        section_sep(self.ctrl_imp, "── Display Settings ──")
        self.imp_type = labeled_seg(self.ctrl_imp, "Plot Mode", ["|Z| Only", "|Z| & Phase"], "|Z| Only", command=lambda _: self.update_imp_plot())
        self.imp_x_scale = labeled_seg(self.ctrl_imp, "X-Axis (Freq)", ["Linear", "Log"], "Linear", command=lambda _: self.update_imp_plot())
        self.imp_y_scale = labeled_seg(self.ctrl_imp, "Y-Axis (|Z|)", ["Linear", "Log"], "Log", command=lambda _: self.update_imp_plot())
        
        section_sep(self.ctrl_imp, "── Loaded Files ──")
        # FIX: Swapped static textbox for an interactive scrollable frame
        self.imp_file_list = ctk.CTkScrollableFrame(self.ctrl_imp, height=150); self.imp_file_list.pack(fill="x", padx=10, pady=5)
        
        self.fig_imp = plt.figure(figsize=(9, 6), facecolor="white"); self.ax_imp_z = self.fig_imp.add_subplot(111); self.ax_imp_p = self.ax_imp_z.twinx(); self.ax_imp_p.set_visible(False)
        self.canvas_imp = FigureCanvasTkAgg(self.fig_imp, master=pf); self.canvas_imp.mpl_connect('pick_event', self._on_legend_pick); self.canvas_imp.mpl_connect('button_press_event', self._on_plot_click)
        
        # FIX: Lock toolbar height
        tf = tk.Frame(pf, bg="#333333", height=40); tf.pack_propagate(False); tf.pack(side="top", fill="x")
        
        self.toolbar_imp = NavigationToolbar2Tk(self.canvas_imp, tf); self.toolbar_imp.update(); self._bind_custom_home(self.toolbar_imp, self.fig_imp)
        
        # FIX: Pack into the toolbar
        self._add_fullscreen_btn(self.toolbar_imp, self.fig_imp, "Impedance Analysis")
        ctk.CTkLabel(pf, text="💡 Tip: Double-click plot to add coordinate markers. Click legends/titles to edit. Click 'Home' 🏠 to reset.", font=("Arial", 11), text_color=("gray50", "gray60")).pack(side="bottom", pady=2)
        self.canvas_imp.get_tk_widget().pack(side="top", fill="both", expand=True)

    def import_imp_csv(self):
        filepaths = filedialog.askopenfilenames(filetypes=[("CSV Files", "*.csv"), ("All Files", "*.*")])
        if not filepaths: return
        for fp in filepaths:
            try:
                freq, z, phase = [], [], []
                with open(fp, 'r') as f: lines = f.readlines()
                start_idx = 0
                for i, line in enumerate(lines):
                    if "Frequency(Hz)" in line or "Hz" in line:
                        start_idx = i + 1; break
                for line in lines[start_idx:]:
                    parts = line.strip().split(',')
                    if len(parts) >= 3:
                        try: freq.append(float(parts[0])); z.append(float(parts[1])); phase.append(float(parts[2]))
                        except ValueError: pass
                if freq and z:
                    name = os.path.splitext(os.path.basename(fp))[0]
                    self.imp_data[name] = (np.array(freq), np.array(z), np.array(phase))
                    self._is_dirty = True
            except Exception as e: self.log(f"Failed to load {os.path.basename(fp)}: {e}")
        self.update_imp_listbox(); self.update_imp_plot()

    def clear_imp_data(self):
        if self.imp_data:
            self.imp_data.clear(); self.update_imp_listbox(); self.update_imp_plot()
            self._is_dirty = True

    def update_imp_listbox(self):
        for widget in self.imp_file_list.winfo_children(): widget.destroy()
        if not self.imp_data:
            ctk.CTkLabel(self.imp_file_list, text="No files loaded.", text_color="gray").pack(pady=10)
        else:
            for name in list(self.imp_data.keys()):
                row_f = ctk.CTkFrame(self.imp_file_list, fg_color="transparent"); row_f.pack(fill="x", pady=2)
                ctk.CTkLabel(row_f, text=f"• {name}", font=("Arial", 11), anchor="w").pack(side="left", fill="x", expand=True)
                ctk.CTkButton(row_f, text="✕", width=24, height=24, fg_color="#c62828", hover_color="#b71c1c", command=lambda n=name: self.remove_imp_file(n)).pack(side="right", padx=(5, 0))

    def remove_imp_file(self, name):
        """Safely removes an individual file from the impedance data and redraws."""
        if name in self.imp_data:
            del self.imp_data[name]
            self.update_imp_listbox()
            self.update_imp_plot()
            self._is_dirty = True

    def update_imp_plot(self):
        self.ax_imp_z.clear(); self.ax_imp_p.clear()
        show_phase = self.imp_type.get() == "|Z| & Phase"
        if not self.imp_data:
            self.ax_imp_z.set_title("Waiting for CSV Data...", color="gray"); self.ax_imp_p.set_visible(False)
            self.canvas_imp.draw(); return
        if len(self.imp_data) > 1 and show_phase:
            self.log("Phase plotting disabled (multiple files). Showing |Z| only."); show_phase = False
        self.ax_imp_p.set_visible(show_phase)
        
        colors = plt.cm.tab10(np.linspace(0, 1, max(10, len(self.imp_data))))
        for idx, (name, (f, z, p)) in enumerate(self.imp_data.items()):
            c = colors[idx % 10]; fk = f / 1000.0
            self.ax_imp_z.plot(fk, z, color=c, lw=1.5, label=name)
            if show_phase: self.ax_imp_p.plot(fk, p, color='#ff9800', lw=1.5, ls='--', alpha=0.9, label=f"{name} (Phase)")
            
        self.ax_imp_z.set_xlabel("Frequency (kHz)"); self.ax_imp_z.set_ylabel("Impedance |Z| (Ω)")
        self.ax_imp_z.set_title("Impedance Spectrum"); self.ax_imp_z.grid(True, alpha=0.3)
        self.ax_imp_z.set_xscale('log' if self.imp_x_scale.get() == "Log" else 'linear')
        self.ax_imp_z.set_yscale('log' if self.imp_y_scale.get() == "Log" else 'linear')
        
        try:
            fmin = float(self.imp_fmin.get()) if self.imp_fmin.get() else None
            fmax = float(self.imp_fmax.get()) if self.imp_fmax.get() else None
            if fmin is not None or fmax is not None:
                self.ax_imp_z.set_xlim(left=fmin, right=fmax)
        except ValueError: pass
        
        if show_phase: self.ax_imp_p.set_ylabel("Phase θ (°)")
        
        h_z, l_z = self.ax_imp_z.get_legend_handles_labels()
        h_p, l_p = self.ax_imp_p.get_legend_handles_labels() if show_phase else ([], [])
        leg = self.ax_imp_z.legend(h_z + h_p, l_z + l_p, loc='best', fontsize=8)
        self.ax_imp_z._master_handles = h_z + h_p; self.ax_imp_z._master_labels = l_z + l_p; self.ax_imp_z._leg_loc = 'best'; self.ax_imp_z._leg_fs = 8
        self._make_legend_interactive(leg, h_z + h_p, self.ax_imp_z)
        self._make_labels_editable(self.ax_imp_z)
        if show_phase: self._make_labels_editable(self.ax_imp_p)
        self.fig_imp.tight_layout(); self.canvas_imp.draw()

    # ------------------------------------------------------------------
    # Hardware Methods
    # ------------------------------------------------------------------
    def _fg_set_continuous(self, waveform="SINusoid", voltage=None):
        self.fg.write("SOURCE1:BURST:STATE OFF"); self.fg.write("SOURCE1:SWEEP:STATE OFF")
        self.fg.write("SOURCE1:AM:STATE OFF"); self.fg.write("SOURCE1:FM:STATE OFF"); self.fg.write("SOURCE1:PM:STATE OFF")
        self.fg.write(f"SOURCE1:FUNCTION {waveform}"); self.fg.write(f"SOURCE1:VOLTAGE {voltage or '20.0'}")

    def _fg_set_burst(self, freq_hz, voltage, cycles, waveform="SINusoid", trig="TRIGgered", idle="0V"):
        self.fg.write("OUTPut1:STATe OFF"); self.fg.write("SOURCE1:SWEEP:STATE OFF")
        self.fg.write("SOURCE1:AM:STATE OFF"); self.fg.write("SOURCE1:FM:STATE OFF"); self.fg.write("SOURCE1:PM:STATE OFF")
        self.fg.write(f"SOURCE1:FUNCTION {waveform}"); self.fg.write("SOURCE1:BURST:STATE ON")
        self.fg.write(f"SOURCE1:VOLTAGE {voltage}"); self.fg.write(f"SOURCE1:FREQUENCY {freq_hz}")
        self.fg.write(f"SOURCE1:BURST:NCYCLES {cycles}"); self.fg.write(f"SOURCE1:BURST:MODE {trig}")
        idle_map = {"0V": "0", "First": "FIRSt", "Last": "LAST"}
        self.fg.write(f"SOURCE1:BURST:IDLE {idle_map.get(idle, '0')}")

    def _fg_set_modulation(self, freq_hz, voltage, waveform, mod_type, mod_freq, mod_depth, mod_wave, mod_source):
        self._fg_set_continuous(waveform=waveform, voltage=voltage); self.fg.write(f"SOURCE1:FREQUENCY {freq_hz}")
        mw = {"Sine":"SINusoid","Square":"SQUare","Ramp":"RAMP"}.get(mod_wave, "SINusoid")
        src = "INT" if mod_source == "Internal" else "EXT"
        if mod_type == "AM":
            for c in [f"SOURCE1:AM:INTernal:FUNCtion {mw}", f"SOURCE1:AM:INTernal:FREQuency {mod_freq}", f"SOURCE1:AM:DEPTh {mod_depth}", f"SOURCE1:AM:SOURce {src}", "SOURCE1:AM:STATE ON"]: self.fg.write(c)
        elif mod_type == "FM":
            for c in [f"SOURCE1:FM:INTernal:FUNCtion {mw}", f"SOURCE1:FM:INTernal:FREQuency {mod_freq}", f"SOURCE1:FM:DEViation {mod_depth}", f"SOURCE1:FM:SOURce {src}", "SOURCE1:FM:STATE ON"]: self.fg.write(c)
        elif mod_type == "PM":
            for c in [f"SOURCE1:PM:INTernal:FUNCtion {mw}", f"SOURCE1:PM:INTernal:FREQuency {mod_freq}", f"SOURCE1:PM:DEViation {mod_depth}", f"SOURCE1:PM:SOURce {src}", "SOURCE1:PM:STATE ON"]: self.fg.write(c)
        elif mod_type == "FSK":
            for c in [f"SOURCE1:FSKey:FREQuency {mod_depth}", f"SOURCE1:FSKey:INTernal:RATE {mod_freq}", f"SOURCE1:FSKey:SOURce {src}", "SOURCE1:FSKey:STATE ON"]: self.fg.write(c)

    def _scope_read_channel_raw(self, channel):
        self.scope.write(f":WAVeform:SOURce {channel}"); self.scope.write(":WAVeform:POINts:MODE RAW")
        self.scope.write(":WAVeform:POINts MAX"); self.scope.write(":WAVeform:FORMat BYTE")
        pre = self.scope.query(":WAVeform:PREamble?").split(',')
        raw = self.scope.query_binary_values(":WAVeform:DATA?", datatype='B')
        volt = (np.array(raw) - float(pre[9])) * float(pre[7]) + float(pre[8])
        if len(raw) > 0:
            is_clipping = max(raw) >= 253 or min(raw) <= 2; span_pct = (max(raw) - min(raw)) / 255.0
        else: is_clipping = False; span_pct = 0.0
        return pre, volt, is_clipping, span_pct

    def _scope_set_acquire(self, mode="Average", averages=32):
        scpi = {"Normal":"NORMal","Average":"AVERage","Peak":"PEAK"}.get(mode, "AVERage")
        self.scope.write(f":ACQuire:TYPE {scpi}")
        if scpi == "AVERage": self.scope.write(f":ACQuire:COUNt {averages}")

    def _scope_measure_cw(self, channel, meas_type="RMS"):
        self.scope.write(":RUN")
        mm = {"RMS":(f":MEASure:VRMS DISPlay,AC,{channel}", f":MEASure:VRMS? DISPlay,AC,{channel}"),
              "Peak":(f":MEASure:VPEak {channel}", f":MEASure:VPEak? {channel}"),
              "Vpp":(f":MEASure:VPP {channel}", f":MEASure:VPP? {channel}")}
        sc, qc = mm.get(meas_type, mm["RMS"]); self.scope.write(sc); time.sleep(0.35)
        try: return float(self.scope.query(qc).strip())
        except: return 0.0

    # ------------------------------------------------------------------
    # Worker Methods
    # ------------------------------------------------------------------
    def start_adv_thread(self):
        self._ping_activity()
        try:
            p = {'f': float(self.adv_f.get())*1000, 'v': self.adv_voltage.get(), 'c': self.adv_cycles.get(),
                 'waveform': self.adv_wave.get(), 'fmin': float(self.adv_fmin.get())*1000, 'fmax': float(self.adv_fmax.get())*1000,
                 'pre': float(self.adv_pre.get())/1000, 'tail': float(self.adv_tail.get())/1000,
                 'acq_mode': self.adv_acq.get(), 'avg_n': int(self.adv_avg_n.get()), 'settle': float(self.adv_settle.get())}
        except ValueError: return self.log("Error: Missing/invalid inputs.")
        threading.Thread(target=self._adv_worker, args=(p,), daemon=True).start()

    def start_cwt_thread(self):
        self._ping_activity()
        try:
            p = {'f': float(self.cwt_f.get())*1000, 'v': self.cwt_voltage.get(), 'c': self.cwt_cycles.get(),
                 'waveform': self.cwt_wave.get(), 'fmin': float(self.cwt_fmin.get())*1000, 'fmax': float(self.cwt_fmax.get())*1000,
                 'pre': float(self.cwt_pre.get())/1000, 'tail': float(self.cwt_tail.get())/1000,
                 'acq_mode': self.cwt_acq.get(), 'avg_n': int(self.cwt_avg_n.get()), 'settle': float(self.cwt_settle.get())}
        except ValueError: return self.log("Error: Missing/invalid inputs.")
        threading.Thread(target=self._cwt_worker, args=(p,), daemon=True).start()

    def start_burst_thread(self):
        self._ping_activity()
        try:
            fmn, fmx = self.fft_fmin.get(), self.fft_fmax.get()
            p = {'f': float(self.burst_f.get() or 0)*1000, 'v': self.burst_voltage.get(), 'c': self.burst_cycles.get(),
                 'waveform': self.burst_wave.get(), 'fg_mode': self.burst_fg_mode.get(),
                 'acq_mode': self.burst_acq.get(), 'avg_n': int(self.burst_avg_n.get()), 'settle': float(self.burst_settle.get()),
                 'capture_t': float(self.burst_capture_time.get()), 'dwell': float(self.burst_dwell.get()),
                 'fft_min': float(fmn)*1000 if fmn else None, 'fft_max': float(fmx)*1000 if fmx else None,
                 't': float(self.temp_entry.get()), 'humidity': float(self.humidity_entry.get()),
                 'eff_v_pa': self._effective_sens_v_pa(), 'dist_lock': self.ref_dist_lock_var.get() == "on",
                 'ref_dist': float(self.ref_dist_entry.get()), 'ringdown_ext': float(self.ringdown_ext.get())/1000 if self.ringdown_ext.get() else 0.0,
                 'mod_type': self.mod_type.get(), 'mod_freq': self.mod_freq.get(), 'mod_depth': self.mod_depth.get(), 'mod_wave': self.mod_wave.get(),
                 'mod_source': self.mod_source.get(), 'idle': '0V'}
            if p['fg_mode'] != 'Continuous' and p['f'] == 0: return self.log("Error: Missing Frequency.")
        except ValueError: return self.log("Error: Missing/invalid inputs.")
        threading.Thread(target=self._burst_worker, args=(p,), daemon=True).start()

    def start_sweep_thread(self):
        self._ping_activity()
        try:
            p = {'s': float(self.start_f.get())*1000, 'e': float(self.end_f.get())*1000, 'st': float(self.step_f.get())*1000,
                 'eff_v_pa': self._effective_sens_v_pa(), 'waveform': self.sweep_wave.get(), 'voltage': self.sweep_voltage.get(),
                 'meas': self.sweep_meas.get(), 'dwell': float(self.sweep_dwell.get()), 'spacing': self.sweep_spacing.get(),
                 'yaxis': self.sweep_yaxis.get(), 'bw_highlight': self.bw_thresh_seg.get()}
        except ValueError: return self.log("Error: Missing/invalid inputs.")
        threading.Thread(target=self._sweep_worker, args=(p,), daemon=True).start()

    def start_polar_thread(self):
        self._ping_activity()
        try:
            p = {'freq': float(self.pol_f.get())*1000, 'waveform': self.polar_wave.get(), 'voltage': self.polar_voltage.get(),
                 'start': int(float(self.pol_start.get())), 'end': int(float(self.pol_end.get())), 'step': int(float(self.pol_step.get())),
                 'dir': self.pol_dir.get(), 'dwell': float(self.pol_dwell.get()), 'overlay': self.pol_overlay.get()}
        except ValueError: return self.log("Error: Missing/invalid inputs.")
        threading.Thread(target=self._polar_worker, args=(p,), daemon=True).start()

    def _adv_worker(self, p):
        try:
            self.is_running = True; self._set_ui_state(True)
            wf = WAVEFORMS.get(p['waveform'], "SINusoid"); cs = f"Burst_{wf}_{p['f']}_{p['v']}_{p['c']}_TRIGgered_0V"
            if self._last_fg_state != cs: self._fg_set_burst(p['f'], p['v'], p['c'], waveform=wf); self._last_fg_state = cs
            
            self._scope_set_acquire(p['acq_mode'], p['avg_n'])
            
            self.fg.write("OUTPut1:STATe ON")
            self.log(f"Waiting {p['settle']}s for signal to settle...")
            time.sleep(p['settle'])
            
            self.scope.timeout = 120000 # Stop USB timeout for long captures
            self.log(f"Digitizing {p['avg_n']} averages...")
            self.scope.write(f":DIGitize {TX_CHANNEL},{RX_CHANNEL}")
            
            pre, mic_v, is_clip, s_pct = self._scope_read_channel_raw(RX_CHANNEL)
            self.fg.write("OUTPut1:STATe OFF")
            
            self.after(0, self._update_level_meter, s_pct, is_clip)
            if is_clip: 
                self.after(0, lambda fhz=p['f'], v=p['v'], w=wf: self.show_clipping_warning(restart_callback=self.start_adv_thread, clip_f_hz=fhz, clip_v=v, clip_w=w, clip_mode="Burst"))
                return
                
            dt, t0 = float(pre[4]), float(pre[5]); t = (np.arange(len(mic_v)) * dt) + t0
            self.last_adv_raw = np.column_stack((t, mic_v))
            env = np.abs(hilbert(mic_v)); pi = np.argmax(env)
            i0, i1 = max(0, pi - int(p['pre']/dt)), min(len(mic_v), pi + int(p['tail']/dt))
            ts, vs = t[i0:i1], mic_v[i0:i1]
            nps = min(int(0.0005/dt), len(vs)//4); nol = int(nps*0.95); nf = max(2048, nps*4)
            fs, ts2, Sxx = spectrogram(vs, fs=1/dt, nperseg=nps, noverlap=nol, nfft=nf)
            self.after(0, lambda: self.update_adv_ui(ts, fs, ts2, Sxx, p['fmin']/1000, p['fmax']/1000))
            self._is_dirty = True
        except Exception as e: self.log(f"STFT Err: {e}")
        finally:
            if self.scope: self.scope.timeout = 5000
            self._set_ui_state(False)

    def _cwt_worker(self, p):
        try:
            self.is_running = True; self._set_ui_state(True)
            wf = WAVEFORMS.get(p['waveform'], "SINusoid"); cs = f"Burst_{wf}_{p['f']}_{p['v']}_{p['c']}_TRIGgered_0V"
            if self._last_fg_state != cs: self._fg_set_burst(p['f'], p['v'], p['c'], waveform=wf); self._last_fg_state = cs
            
            self._scope_set_acquire(p['acq_mode'], p['avg_n'])
            
            self.fg.write("OUTPut1:STATe ON")
            self.log(f"Waiting {p['settle']}s for signal to settle...")
            time.sleep(p['settle'])
            
            self.scope.timeout = 120000 # Stop USB timeout for long captures
            self.log(f"Digitizing {p['avg_n']} averages...")
            self.scope.write(f":DIGitize {TX_CHANNEL},{RX_CHANNEL}")
            
            pre, mic_v, is_clip, s_pct = self._scope_read_channel_raw(RX_CHANNEL)
            self.fg.write("OUTPut1:STATe OFF")
            
            self.after(0, self._update_level_meter, s_pct, is_clip)
            if is_clip: 
                self.after(0, lambda fhz=p['f'], v=p['v'], w=wf: self.show_clipping_warning(restart_callback=self.start_cwt_thread, clip_f_hz=fhz, clip_v=v, clip_w=w, clip_mode="Burst"))
                return
                
            dt, t0 = float(pre[4]), float(pre[5]); t = (np.arange(len(mic_v)) * dt) + t0
            self.last_cwt_raw = np.column_stack((t, mic_v))
            env = np.abs(hilbert(mic_v)); pi = np.argmax(env)
            i0, i1 = max(0, pi-int(p['pre']/dt)), min(len(mic_v), pi+int(p['tail']/dt))
            ts, vs = t[i0:i1], mic_v[i0:i1]
            fhz = np.linspace(p['fmin'], p['fmax'], 150); cf = pywt.central_frequency('cmor15.0-1.0')
            scales = cf / (fhz * dt); coefs, _ = pywt.cwt(vs, scales, 'cmor15.0-1.0', sampling_period=dt)
            self.after(0, lambda tm=ts, fr=fhz, z=np.abs(coefs): self.update_cwt_ui(tm, fr, z))
            self._is_dirty = True
        except Exception as e: self.log(f"CWT Err: {e}")
        finally: 
            if self.scope: self.scope.timeout = 5000
            self._set_ui_state(False)

    def _burst_worker(self, p):
        try:
            self.is_running = True; self._set_ui_state(True)
            sos = 331.3 * np.sqrt(1 + p['t'] / 273.15)
            eff_v_pa = p['eff_v_pa']; wf = WAVEFORMS.get(p['waveform'], "SINusoid"); fm = p['fg_mode']
            tof_valid = p['waveform'] == "Sine" and fm == "Burst"

            cs = f"{fm}_{wf}_{p.get('f','')}_{p['v']}_{p['c']}_TRIGgered_{p.get('idle','0V')}"
            if self._last_fg_state != cs:
                if fm == "Burst": self._fg_set_burst(p['f'], p['v'], p['c'], waveform=wf, idle=p['idle'])
                elif fm == "Continuous": self._fg_set_continuous(waveform=wf, voltage=p['v']); self.fg.write(f"SOURCE1:FREQUENCY {p['f']}")
                elif fm == "Modulation": self._fg_set_modulation(p['f'], p['v'], wf, p['mod_type'], p['mod_freq'], p['mod_depth'], p['mod_wave'], p['mod_source'])
                self._last_fg_state = cs

            self._scope_set_acquire(p['acq_mode'], p['avg_n'])
            
            self.fg.write("OUTPut1:STATe ON")
            self.log(f"Waiting {p['settle']}s for signal to settle...")
            time.sleep(p['settle'])
            
            self.scope.timeout = 120000 # Stop USB timeout for long captures
            self.log(f"Digitizing {p['avg_n']} averages...")
            self.scope.write(f":DIGitize {TX_CHANNEL},{RX_CHANNEL}")
            
            # The script FG on duration (this does NOT change scope timebase)
            time.sleep(p['capture_t']) 
            self.fg.write("OUTPut1:STATe OFF")
            time.sleep(p['dwell'])

            data, pre_list = [], []
            for ch in [TX_CHANNEL, RX_CHANNEL]:
                pre, volt, is_clip, span_pct = self._scope_read_channel_raw(ch)
                pre_list.append(pre); data.append(volt)
                if ch == RX_CHANNEL:
                    self.after(0, self._update_level_meter, span_pct, is_clip)
                    if is_clip: 
                        self.after(0, lambda fhz=p.get('f'), v=p['v'], w=wf, m=fm: self.show_clipping_warning(restart_callback=self.start_burst_thread, clip_f_hz=fhz, clip_v=v, clip_w=w, clip_mode=m))
                        return

            mic_v = data[1]
            dt, t0 = float(pre_list[1][4]), float(pre_list[1][5]); t = (np.arange(len(mic_v)) * dt) + t0
            self.last_burst_t = t; self.last_burst_tx = data[0]; self.last_burst_mic = mic_v; self._last_burst_pre_list = pre_list

            vpp_scope = np.max(mic_v) - np.min(mic_v); vpp_pa = vpp_scope / eff_v_pa
            env1 = np.abs(hilbert(data[0])); env2 = np.abs(hilbert(mic_v)); self._last_burst_env2 = env2
            noise_rms, ns, ne = self._auto_noise_rms(mic_v, env2, pre_list)
            self._last_noise_rms = noise_rms; self._last_noise_range = (ns, ne)

            sig_std = np.std(mic_v)
            eff_noise = np.sqrt(max(0, noise_rms**2 + self._calibrated_noise_rms**2))
            
            snr_db = 20 * np.log10(sig_std / eff_noise) if eff_noise > 0 else 0
            peak_pa = (np.max(env2) / eff_v_pa) / np.sqrt(2); peak_spl = 20 * np.log10(peak_pa / 20e-6) if peak_pa > 0 else 0
            freq_hz = p['f']; alpha_db_m = atmospheric_absorption_db_per_m(freq_hz, p['t'], p['humidity'])
            
            dist_m = None; dist_text = "N/A"; sl_text = "SL@1m: N/A"
            a1 = np.where(env1 > (np.max(env1) * 0.2))[0]; a2 = np.where(env2 > (np.max(env2) * 0.15))[0]
            if len(a1) > 0 and len(a2) > 0:
                tof_dist_cm = ((t[a2[0]] - t[a1[0]]) * sos) * 100
                if tof_valid: dist_text = f"{tof_dist_cm:.2f} cm"
                if p['dist_lock'] and p['ref_dist'] > 0: dist_m = p['ref_dist'] / 100.0
                elif tof_valid and tof_dist_cm > 0: dist_m = tof_dist_cm / 100.0
                if dist_m and dist_m > 0.01:
                    sl_text = f"SL@1m: {peak_spl + 20 * np.log10(dist_m) + alpha_db_m * dist_m:.1f} dB"

            f2 = np.fft.rfftfreq(len(mic_v), dt); m2 = np.abs(np.fft.rfft(mic_v))
            self.last_burst_fft_f = f2; self.last_burst_fft_m = m2
            thd_pct, harm_mags = self._calculate_thd(f2, m2, freq_hz)
            thd_text = f"THD: {thd_pct:.1f}%"
            thd_warn = "⚠ HIGH THD — Reduce drive voltage!" if thd_pct > 10 else "⚡ Moderate THD — transducer may be non-linear" if thd_pct > 5 else ""
            tau, rd_peak, rd_end = self._calculate_ringdown(env2, dt, drop_db=20)
            tau_text = f"τ₂₀: {tau*1000:.3f} ms" if tau else "τ₂₀: N/A"
            extra_tail_ms = p.get('ringdown_ext', 0)
            mode_txt = "manual" if self._noise_override else "auto"

            self.after(0, lambda nr=noise_rms, ns_=ns, ne_=ne, mt=mode_txt: self.noise_info_lbl.configure(text=f"σ: {nr:.6f} V [{ns_}:{ne_}] ({mt})"))
            self.after(0, lambda dt_=dist_text, snr=snr_db, vs=vpp_scope, vp=vpp_pa, sp=peak_spl, sl=sl_text, thd=thd_text, tw=thd_warn, tau_t=tau_text, ab=alpha_db_m: (
                self.dist_lbl.configure(text=dt_), self.snr_lbl.configure(text=f"{snr:.1f} dB SNR"),
                self.vpp_scope_lbl.configure(text=f"Scope:  {vs:.3f} V"), self.vpp_pa_lbl.configure(text=f"Acoustic: {vp:.3f} Pa"),
                self.spl_lbl.configure(text=f"{sp:.1f} dB SPL"), self.sl_lbl.configure(text=sl),
                self.thd_lbl.configure(text=thd, text_color=("#c62828","#ff5252") if "HIGH" in tw else ("gray40","gray70")),
                self.thd_warn_lbl.configure(text=tw), self.tau_lbl.configure(text=tau_t),
                self.dash_vpp.configure(text=f"{vs:.3f} V"), self.dash_pa.configure(text=f"{vp:.3f} Pa"),
                self.dash_spl.configure(text=f"{sp:.1f} dB SPL"), self.dash_sl.configure(text=sl),
                self.dash_snr.configure(text=f"{snr:.1f} dB SNR"), self.dash_dist.configure(text=dt_),
                self.dash_thd.configure(text=thd, text_color=("#c62828","#ff5252") if "HIGH" in tw else ("gray40","gray70")),
                self.dash_tau.configure(text=tau_t)
            ))

            tm = t * 1000
            if len(a1) > 0 and len(a2) > 0:
                a2_tail = np.where(env2 > (np.max(env2) * 0.03))[0]
                plot_end_idx = a2_tail[-1] if len(a2_tail) > 0 else a2[-1]
                cs_, ce = tm[a1[0]] - 0.3, tm[plot_end_idx] + 0.5 + extra_tail_ms
                ss, se  = tm[a2[0]] - 0.3, tm[plot_end_idx] + 0.5 + extra_tail_ms
            else:
                cs_, ce = tm[0], tm[-1]; ss, se = tm[0], tm[-1]
                
            ce = min(ce, tm[-1]); se = min(se, tm[-1]); cs_ = max(cs_, tm[0]); ss = max(ss, tm[0])
            self.after(0, lambda: self.update_burst_ui(tm, data[0], mic_v, env2, f2, m2, eff_v_pa, cs_, ce, ss, se, p['fft_min'], p['fft_max'], noise_rms, ns, ne, freq_hz, thd_pct, harm_mags, tau, rd_peak, rd_end))
            if alpha_db_m > 0: self.log(f"Absorption: {alpha_db_m:.4f} dB/m @ {freq_hz/1000:.1f} kHz, {p['humidity']}% RH")
            self._is_dirty = True
        except Exception as e: self.log(f"Burst Err: {e}")
        finally: 
            if self.scope: self.scope.timeout = 5000
            self._set_ui_state(False)

    def _sweep_worker(self, p):
        try:
            self.is_running = True; self._set_ui_state(True); self._last_fg_state = None
            eff_v_pa = p['eff_v_pa']; wf = WAVEFORMS.get(p['waveform'], "SINusoid")
            f_l, v_l, pa_l, s_l = [], [], [], []
            self.after(0, lambda: self.clear_bw_plot())
            if p['spacing'] == "Log": steps = np.geomspace(p['s'], p['e'], int((p['e']-p['s'])/p['st'])+1)
            else: steps = np.arange(p['s'], p['e']+p['st'], p['st'])
            total = len(steps)
            self._fg_set_continuous(waveform=wf, voltage=str(p['voltage'])); self.fg.write("OUTPut1:STATe ON")
            self._scope_set_acquire("Normal")

            for idx, f in enumerate(steps):
                if not self.is_running: break
                pct = (idx+1)/total
                self.after(0, lambda p_=pct: (self.sweep_progress.set(p_), self.sweep_prog_lbl.configure(text=f"{int(p_*100)}%")))
                self.fg.write(f"SOURCE1:FREQUENCY {f}"); time.sleep(p['dwell'])
                v_raw = self._scope_measure_cw(RX_CHANNEL, p['meas'])
                v_rms = v_raw/(2*np.sqrt(2)) if p['meas']=="Vpp" else v_raw/np.sqrt(2) if p['meas']=="Peak" else v_raw
                try:
                    scale = float(self.scope.query(f":{RX_CHANNEL}:SCALe?"))
                    vpp_est = v_rms * 2.828; span_pct = min(1.0, vpp_est / (scale * 8)); is_clip = span_pct >= 0.95
                    self.after(0, lambda sp=span_pct, ic=is_clip: self._update_level_meter(sp, ic))
                    if is_clip: 
                        self.fg.write("OUTPut1:STATe OFF")
                        self.after(0, lambda fhz=f, v=p['voltage'], w=wf: self.show_clipping_warning(restart_callback=self.start_sweep_thread, clip_f_hz=fhz, clip_v=v, clip_w=w, clip_mode="Continuous"))
                        return
                except: pass

                pa_rms = v_rms / eff_v_pa; spl = 20*np.log10(pa_rms/20e-6 + 1e-18)
                f_l.append(f/1000); v_l.append(v_rms); pa_l.append(pa_rms); s_l.append(spl)
                y_disp = {"SPL (dB)": s_l, "Pa RMS": pa_l, "V RMS": v_l}[p['yaxis']]
                self.after(0, lambda fl=list(f_l), yl=list(y_disp), ax=p['yaxis']: self.update_sw_plot(fl, yl, ax))
            
            self.fg.write("OUTPut1:STATe OFF"); self.last_sweep_data = np.column_stack((f_l, v_l, pa_l, s_l))

            if len(s_l) >= 3:
                s_arr = np.array(s_l); f_arr = np.array(f_l)
                peak_idx = int(np.argmax(s_arr)); peak_freq = f_arr[peak_idx]
                bw_results = {}
                for label, db_drop in BW_THRESHOLDS.items():
                    thresh = s_arr[peak_idx] - db_drop
                    li, ri = 0, len(s_arr)-1
                    for i in range(peak_idx, -1, -1):
                        if s_arr[i] < thresh: li = i; break
                    for i in range(peak_idx, len(s_arr)):
                        if s_arr[i] < thresh: ri = i; break
                    bw = f_arr[ri] - f_arr[li]
                    q  = peak_freq / bw if bw > 0 else float('inf')
                    bw_results[db_drop] = {'bw': bw, 'q': q, 'li': li, 'ri': ri}

                bw3 = bw_results[3.0]['bw']; q3 = bw_results[3.0]['q']
                highlight_db = BW_THRESHOLDS.get(p['bw_highlight'], 3.0); active_bw = bw_results[highlight_db]['bw']
                
                def update_labels():
                    self.peak_f_lbl.configure(text=f"Peak: {peak_freq:.3f} kHz"); self.q_lbl.configure(text=f"Q: {q3:.1f}")
                    self.dash_peak_f.configure(text=f"{peak_freq:.3f} kHz"); self.dash_bw_title.configure(text=f"Bandwidth ({p['bw_highlight']})")
                    self.dash_bw.configure(text=f"{active_bw:.3f} kHz"); self.dash_q.configure(text=f"{q3:.1f}")
                    for db_val, lbl in self.bw_labels.items():
                        r = bw_results.get(db_val)
                        if r: lbl.configure(text=f"-{int(db_val)}dB: {r['bw']:.3f} kHz (Q={r['q']:.1f})")
                self.after(0, update_labels)
                self.after(0, lambda: self.update_sw_bw_plot(f_arr, s_arr, peak_idx, bw_results, highlight_db, q3, peak_freq, bw3))
            self._is_dirty = True
        except Exception as e: self.log(f"Sweep Err: {e}")
        finally:
            self.after(0, lambda: self.sweep_prog_lbl.configure(text="Finished")); self._set_ui_state(False)

    def _polar_worker(self, p):
        try:
            self.is_running = True; self._set_ui_state(True); self._last_fg_state = None
            wf = WAVEFORMS.get(p['waveform'], "SINusoid"); pol_min = int(float(self.pol_range.get()))
            self._fg_set_continuous(waveform=wf, voltage=str(p['voltage']))
            self.fg.write(f"SOURCE1:FREQUENCY {p['freq']}"); self.fg.write("OUTPut1:STATe ON")
            angles = list(range(p['start'], p['end']+p['step'], p['step']))
            if p['dir'] == "End→Start": angles = list(reversed(angles))
            elif p['dir'] == "Both": angles = angles + list(reversed(angles[:-1]))
            total = len(angles)
            self.arduino.write(f"G{angles[0]}\n".encode()); time.sleep(4)
            al, vl = [], []; self._scope_set_acquire("Normal")
            
            for idx, deg in enumerate(angles):
                if not self.is_running: break
                self.after(0, lambda p_=(idx+1)/total: (self.polar_progress.set(p_), self.polar_prog_lbl.configure(text=f"{int(p_*100)}%")))
                self.arduino.write(f"G{deg}\n".encode()); time.sleep(p['dwell'])
                v_rms = self._scope_measure_cw(RX_CHANNEL, "RMS")
                vl.append(v_rms); al.append(np.radians(deg))
                try:
                    scale = float(self.scope.query(f":{RX_CHANNEL}:SCALe?"))
                    vpp_est = v_rms * 2.828; span_pct = min(1.0, vpp_est / (scale * 8)); is_clip = span_pct >= 0.95
                    self.after(0, lambda sp=span_pct, ic=is_clip: self._update_level_meter(sp, ic))
                    if is_clip: 
                        self.fg.write("OUTPut1:STATe OFF"); self.arduino.write(b"G0\n")
                        self.after(0, lambda fhz=p['freq'], v=p['voltage'], w=wf: self.show_clipping_warning(restart_callback=self.start_polar_thread, clip_f_hz=fhz, clip_v=v, clip_w=w, clip_mode="Continuous"))
                        return
                except: pass
                
                self.after(0, lambda a=list(al), v=list(vl), pm=pol_min: self.update_polar_ui(a, v, pm))
                
            mx = max(vl) or 1; norm = [20*np.log10(v/mx) for v in vl]
            self.last_polar_data = np.column_stack((al, norm))
            if p['overlay'] == "Overlay": self._polar_overlays.append((list(al), list(norm)))
            self.fg.write("OUTPut1:STATe OFF"); self.arduino.write(b"G0\n")
            try:
                sp = sorted(zip(angles, norm)); sa = [x[0] for x in sp]; sn = [x[1] for x in sp]; pi = np.argmax(sn)
                def fb(th):
                    l, r = pi, pi
                    while l > 0 and sn[l] > th: l -= 1
                    while r < len(sn)-1 and sn[r] > th: r += 1
                    return f"{abs(sa[r]-sa[l]):.1f}" if sn[l] <= th and sn[r] <= th else "--"
                bw3, bw6 = fb(-3.0), fb(-6.0)
            except: bw3, bw6 = "--", "--"
            self.after(0, lambda: (self.pol_bw3_lbl.configure(text=f"-3dB: {bw3} °"), self.pol_bw6_lbl.configure(text=f"-6dB: {bw6} °"), self.dash_bw3.configure(text=f"{bw3} °"), self.dash_bw6.configure(text=f"{bw6} °")))
            self._is_dirty = True
        except Exception as e: self.log(f"Polar Err: {e}")
        finally: self.after(0, lambda: self.polar_prog_lbl.configure(text="Finished")); self._set_ui_state(False)

    # ------------------------------------------------------------------
    # Prediction Methods
    # ------------------------------------------------------------------
    def update_polar_prediction(self, *args):
        """Redraws the current polar view with the theoretical overlay if enabled."""
        pol_min = int(float(self.pol_range.get()))
        self.update_polar_ui(pol_min=pol_min)

    def _calculate_theoretical_pattern(self, angles_rad):
        """Calculates normalized pressure pattern based on shape geom, modes, and frequency."""
        try:
            freq_hz = float(self.pol_f.get() or "40.0") * 1000
            temp_c = float(self.temp_entry.get() or "20.0")
            sos = 331.3 * np.sqrt(1 + temp_c / 273.15)
            k = (2 * np.pi * freq_hz) / sos
            
            dim_mm = float(self.pred_dim.get() or "10.0")
            a = (dim_mm / 1000.0) / 2.0  # Radius (Circular) or Half-width (Rectangular)
            
            n = int(self.pred_mode_n.get() or "0")
            m = int(self.pred_mode_m.get() or "0")
            
            geom = self.pred_geom.get()
            
            # Fully vectorized calculation for massive performance and precision
            X = k * a * np.sin(angles_rad)
            # Use a small epsilon for X to avoid divide-by-zero warnings/errors at theta=0
            X_safe = np.where(np.abs(X) > 1e-9, X, 1e-9)
            
            if geom == "Circular":
                # Edge-clamped flexural plate directivity for all modes (including fundamental 0,0)
                # Perfect for HIFFUTs and flexural ultrasonics
                m_safe = max(0, m)
                n_safe = max(0, n)
                
                # Base directivity for modal patterns based on Bessel roots
                root = jn_zeros(m_safe, n_safe + 1)[n_safe]
                denom = root**2 - X_safe**2
                
                # Prevent NaN proliferation by masking 0s before division occurs
                safe_denom = np.where(np.abs(denom) < 1e-9, 1e-9, denom)
                
                limit_val = np.abs((jn(m_safe-1, X_safe) - jn(m_safe+1, X_safe)) / (4.0 * X_safe))
                normal_val = np.abs(jn(m_safe, X_safe) / safe_denom)
                
                # Safely apply L'Hopital limit at singularities
                val = np.where(np.abs(denom) < 1e-6, limit_val, normal_val)
            else:
                # Rectangular Flexural Plate
                mu = n + 1
                denom = X_safe**2 - (mu * np.pi / 2.0)**2
                
                # Prevent NaN proliferation
                safe_denom = np.where(np.abs(denom) < 1e-9, 1e-9, denom)
                
                limit_val = np.abs(1.0 / (mu * np.pi))
                if n % 2 == 0:  # Even n -> Symmetric modes
                    normal_val = np.abs(np.cos(X_safe) / safe_denom)
                else:           # Odd n -> Asymmetric modes
                    normal_val = np.abs(np.sin(X_safe) / safe_denom)
                
                val = np.where(np.abs(denom) < 1e-6, limit_val, normal_val)
                
            # Smoothly taper the extreme edges (85 to 90 degrees) to 0 pressure. 
            # This elegantly forces the lobes to close at the graph origin (-30 dB) 
            # WITHOUT drawing artificial horizontal dashed lines across the grid.
            taper_start = np.radians(85)
            edge_taper = np.where(np.abs(angles_rad) > taper_start,
                                  np.cos(np.pi/2 * (np.abs(angles_rad) - taper_start) / (np.pi/2 - taper_start))**2,
                                  1.0)
            val = val * edge_taper
                
            # Clean up any lingering NaNs, normalize to Max, and convert to dB
            val = np.nan_to_num(val, nan=1e-12, posinf=1e-12, neginf=1e-12)
            mx = np.max(val)
            if mx > 0: val /= mx
            return 20 * np.log10(val + 1e-12)
        except Exception as e:
            self.log(f"Prediction Err: {e}")
            return None

    def _update_burst_separation(self, val):
        """Dynamically adjusts the Y-axis limits to visually separate the TX and RX plots."""
        if hasattr(self, 'ax_c') and hasattr(self, 'ax_ct') and hasattr(self, '_burst_tx_mx'):
            sep = float(val)
            self.ax_c.set_ylim(-sep * self._burst_tx_mx, 1.2 * self._burst_tx_mx)
            self.ax_ct.set_ylim(-1.2 * self._burst_rx_mx, sep * self._burst_rx_mx)
            self.fig_b.canvas.draw_idle()
            self._is_dirty = True

    # ------------------------------------------------------------------
    # Graph Renderers
    # ------------------------------------------------------------------
    def update_adv_ui(self, tm, f_stft, t_stft, Sxx, fmin_k, fmax_k):
        self._last_adv_kwargs = {k:v for k,v in locals().items() if k != 'self'}
        self.fig_adv.clf(); ax = self.fig_adv.add_subplot(111)
        Sdb = 10*np.log10(Sxx+1e-12); vm = np.max(Sdb)
        cax = ax.pcolormesh((t_stft+tm[0])*1000, f_stft/1000, Sdb, shading='gouraud', cmap='jet', vmin=vm-40, vmax=vm)
        self.fig_adv.colorbar(cax, ax=ax, label='Power (dB)')
        ax.set_title("STFT Spectrogram"); ax.set_ylabel("Freq (kHz)"); ax.set_xlabel("Time (ms)")
        ax.set_ylim(fmin_k, fmax_k); ax.set_xlim(tm[0]*1000, tm[-1]*1000)
        self._make_labels_editable(ax)
        self.fig_adv.tight_layout(); self.canvas_adv.draw()

    def update_cwt_ui(self, tm, freqs_hz, cwt_mat):
        self._last_cwt_kwargs = {k:v for k,v in locals().items() if k != 'self'}
        self.fig_cwt.clf(); ax = self.fig_cwt.add_subplot(111)
        cax = ax.pcolormesh(tm*1000, freqs_hz/1000, cwt_mat, shading='gouraud', cmap='jet')
        self.fig_cwt.colorbar(cax, ax=ax, label='Magnitude')
        ax.set_xlabel("Time (ms)"); ax.set_ylabel("Freq (kHz)"); ax.set_title("Wavelet Transform (CWT)")
        self._make_labels_editable(ax)
        self.fig_cwt.tight_layout(); self.canvas_cwt.draw()

    def update_burst_ui(self, tm, ch1, ch2, env2, f2, m2, eff_v_pa, cs, ce, ss, se, fft_min, fft_max, noise_rms, ns, ne, freq_hz=0, thd_pct=0, harm_mags=None, tau=None, rd_peak=0, rd_end=0):
        self._last_burst_kwargs = {k:v for k,v in locals().items() if k != 'self'}
        self.fig_b.clf()
        gs = self.fig_b.add_gridspec(2, 2)
        self.ax_c = self.fig_b.add_subplot(gs[0, 0]); self.ax_ct = self.ax_c.twinx()
        ax_s = self.fig_b.add_subplot(gs[0, 1]); ax_f = self.fig_b.add_subplot(gs[1, :])

        self._burst_tx_mx = max(np.max(np.abs(ch1)), 1)
        self._burst_rx_mx = max(np.max(np.abs(ch2*1000)), 1)
        sep = float(self.burst_sep_slider.get())

        self.ax_c.plot(tm, ch1, color='red', alpha=0.6, label='TX (V)', lw=1)
        self.ax_c.set_xlim(cs, ce); self.ax_c.set_ylim(-sep*self._burst_tx_mx, 1.2*self._burst_tx_mx)
        self.ax_c.set_xlabel("Time (ms)"); self.ax_c.set_ylabel("TX (V)", color='red'); self.ax_c.tick_params(axis='y', colors='red')
        self.ax_ct.plot(tm, ch2*1000, color='blue', alpha=0.8, label='RX (mV)', lw=1)
        self.ax_ct.set_ylim(-1.2*self._burst_rx_mx, sep*self._burst_rx_mx); self.ax_ct.set_ylabel("RX (mV)", color='blue'); self.ax_ct.tick_params(axis='y', colors='blue')
        self.ax_c.set_title("TX & RX Signals")
        l1, lb1 = self.ax_c.get_legend_handles_labels(); l2, lb2 = self.ax_ct.get_legend_handles_labels()
        leg_c = self.ax_c.legend(l1+l2, lb1+lb2, loc='upper right', fontsize=8)
        self.ax_c._master_handles = l1+l2; self.ax_c._master_labels = l1+l2; self.ax_c._leg_loc = 'upper right'; self.ax_c._leg_fs = 8
        self._make_legend_interactive(leg_c, l1+l2, self.ax_c)
        self._make_labels_editable(self.ax_c); self._make_labels_editable(self.ax_ct)

        noise_pa = noise_rms / eff_v_pa
        ax_s.axhspan(-noise_pa, noise_pa, color='gray', alpha=0.3, label=f'Noise ±{noise_pa:.4f} Pa')
        ax_s.fill_between(tm, -env2/eff_v_pa, env2/eff_v_pa, color='red', alpha=0.2, label='Envelope')
        ax_s.plot(tm, ch2/eff_v_pa, color='red', lw=0.5, label='Signal')
        if tau is not None and rd_peak < len(tm) and rd_end < len(tm):
            ax_s.axvline(tm[rd_peak], color='#00695c', ls='--', lw=1.5, alpha=0.7, label=f'Peak')
            ax_s.axvline(tm[rd_end], color='#00695c', ls=':', lw=1.5, alpha=0.7, label=f'-20dB ({tau*1000:.2f}ms)')
        
        ax_s.set_xlim(ss, se); ax_s.set_xlabel("Time (ms)"); ax_s.set_ylabel("Pressure (Pa)")
        ax_s.set_title("RX Acoustic Pressure + Ring-Down")
        leg_s = ax_s.legend(loc='upper right', fontsize=7)
        h_s, l_s = ax_s.get_legend_handles_labels()
        ax_s._master_handles = h_s; ax_s._master_labels = l_s; ax_s._leg_loc = 'upper right'; ax_s._leg_fs = 7
        self._make_legend_interactive(leg_s, h_s, ax_s)
        self._make_labels_editable(ax_s)

        ax_f.plot(f2/1000, m2, color='blue', lw=0.8)
        if harm_mags and freq_hz > 0:
            df = f2[1] - f2[0]; sw = max(1, int(200/df))
            for n in range(len(harm_mags)):
                hf = freq_hz * (n + 1)
                if hf/1000 > (fft_max/1000 if fft_max else f2[-1]/1000): break
                color = '#2e7d32' if n == 0 else '#c62828'
                
                # FIX: Removed the "if n < 4" limit so every drawn harmonic gets a legend entry
                label = 'Fundamental' if n == 0 else f'H{n+1}'
                
                ax_f.axvline(hf/1000, color=color, ls='--', lw=1, alpha=0.5, label=label)
            if thd_pct > 0:
                warn_color = '#c62828' if thd_pct > 10 else '#e65100' if thd_pct > 5 else '#2e7d32'
                thd_txt = ax_f.text(0.98, 0.95, f'THD = {thd_pct:.1f}%', transform=ax_f.transAxes, ha='right', va='top', fontsize=12, fontweight='bold', color=warn_color, bbox=dict(boxstyle='round,pad=0.3', facecolor='white', edgecolor=warn_color, alpha=0.9), picker=5)
                thd_txt._is_thd_box = True
            leg_f = ax_f.legend(loc='upper left', fontsize=7)
            h_f, l_f = ax_f.get_legend_handles_labels()
            ax_f._master_handles = h_f; ax_f._master_labels = l_f; ax_f._leg_loc = 'upper left'; ax_f._leg_fs = 7
            self._make_legend_interactive(leg_f, h_f, ax_f)
            
        ax_f.set_xlabel("Freq (kHz)"); ax_f.set_ylabel("Magnitude"); ax_f.set_title("RX FFT + Harmonic Analysis")
        if fft_min is not None and fft_max is not None: ax_f.set_xlim(fft_min/1000, fft_max/1000)
        self._make_labels_editable(ax_f)
        
        # FIX: Re-activate label editing for every subplot on the Burst tab
        for ax in self.fig_b.axes:
            self._make_labels_editable(ax)
            
        self.fig_b.tight_layout(); self.canvas_b.draw()

    def update_sw_plot(self, f, y, yaxis):
        self.ax_sw.clear(); self.ax_sw.plot(f, y, 'b-o', markersize=3)
        self.ax_sw.set_xlabel("Freq (kHz)")
        self.ax_sw.set_ylabel({"SPL (dB)":"SPL (dB re 20µPa)","Pa RMS":"Pa RMS","V RMS":"V RMS"}.get(yaxis, yaxis))
        self.ax_sw.grid(True, alpha=0.3)
        self._make_labels_editable(self.ax_sw)
        self.fig_sw.tight_layout(); self.canvas_sw.draw()

    def clear_bw_plot(self):
        for ax in [self.ax_bw, self.ax_qgauge]:
            ax.clear(); ax.set_xticks([]); ax.set_yticks([]); ax.set_title("Waiting...", fontsize=10, color="gray")
        self.canvas_sw.draw()

    def update_sw_bw_plot(self, f, s, peak_i, bw_results, highlight_db, q_val, peak_freq, bw3):
        self._last_sw_bw_kwargs = {k:v for k,v in locals().items() if k != 'self'}
        self.ax_bw.clear()
        hr = bw_results[highlight_db]; li, ri = hr['li'], hr['ri']
        pad = max(2, int((ri-li)*0.5)); s_i = max(0, li-pad); e_i = min(len(f)-1, ri+pad)
        self.ax_bw.plot(f[s_i:e_i+1], s[s_i:e_i+1], 'b-o', markersize=4)
        
        colors = {3.0: '#d84315', 6.0: '#e65100', 10.0: '#f9a825', 20.0: '#757575'}
        for db_val, r in bw_results.items():
            thresh = s[peak_i] - db_val
            c = colors.get(db_val, 'gray'); alpha = 1.0 if db_val == highlight_db else 0.4
            lw = 2 if db_val == highlight_db else 1
            self.ax_bw.axhline(thresh, color=c, ls='--', lw=lw, alpha=alpha, label=f'-{int(db_val)}dB')
            if db_val == highlight_db:
                self.ax_bw.axvline(f[r['li']], color='green', ls=':', lw=1.5)
                self.ax_bw.axvline(f[r['ri']], color='green', ls=':', lw=1.5)
                self.ax_bw.fill_between(f[r['li']:r['ri']+1], thresh, s[r['li']:r['ri']+1], color='green', alpha=0.2)

        self.ax_bw.set_title(f"-{int(highlight_db)}dB BW: {hr['bw']:.3f} kHz", color='green', fontweight='bold')
        self.ax_bw.set_xlabel("Freq (kHz)"); self.ax_bw.set_ylabel("SPL (dB)"); self.ax_bw.grid(True, alpha=0.3)
        leg_bw = self.ax_bw.legend(fontsize=7, loc='lower center')
        h_bw, l_bw = self.ax_bw.get_legend_handles_labels()
        self.ax_bw._master_handles = h_bw; self.ax_bw._master_labels = l_bw; self.ax_bw._leg_loc = 'lower center'; self.ax_bw._leg_fs = 7
        self._make_legend_interactive(leg_bw, h_bw, self.ax_bw)
        self._make_labels_editable(self.ax_bw)
        self._draw_q_gauge(q_val, peak_freq, bw3)
        self.fig_sw.tight_layout(); self.canvas_sw.draw()

    def _draw_q_gauge(self, q_val, peak_freq=None, bw_val=None):
        ax = self.ax_qgauge; ax.clear(); ax.set_aspect('equal')
        
        # FIX: Deepened the Y-axis lower limit to -1.2 to fully un-squish the bottom text
        ax.set_xlim(-1.4, 1.4); ax.set_ylim(-1.2, 1.4); ax.axis('off')
        
        if q_val is None or q_val == float('inf'):
            ax.text(0, 0.5, "Q: --", ha='center', va='center', fontsize=16, color='gray'); return
            
        q_max = 60; q_c = min(max(q_val, 0), q_max)
        for i in range(100):
            t0 = np.pi + (0-np.pi)*i/100; t1 = np.pi + (0-np.pi)*(i+1)/100; frac = i/100
            if frac < 0.33: r, g, b = 0.9, 0.2+1.6*frac, 0.1
            elif frac < 0.66: r, g, b = 0.9-2.7*(frac-0.33), 0.8, 0.1
            else: r, g, b = 0.1, 0.8-0.3*(frac-0.66), 0.2
            arc = np.linspace(t0, t1, 5)
            ax.fill(np.concatenate([0.7*np.cos(arc), np.cos(arc[::-1])]), np.concatenate([0.7*np.sin(arc), np.sin(arc[::-1])]), color=(r,g,b), alpha=0.6)
            
        na = np.pi + (0-np.pi)*(q_c/q_max)
        ax.plot([0, 0.95*np.cos(na)], [0, 0.95*np.sin(na)], 'k-', lw=3, solid_capstyle='round'); ax.plot(0, 0, 'ko', ms=8, zorder=5)
        
        # FIX: Spread the Y-coordinates out drastically (-0.3, -0.65, -0.95) to prevent overlap
        ax.text(0, -0.3, f"Q = {q_val:.1f}", ha='center', va='center', fontsize=15, fontweight='bold', color='#1a237e')
        for qt in [0, 10, 20, 30, 40, 50, 60]:
            a = np.pi+(0-np.pi)*(qt/q_max); ax.text(1.15*np.cos(a), 1.15*np.sin(a), str(qt), ha='center', va='center', fontsize=7, color='gray')
            
        if q_val<8: d,c = "Very Lossy","#c62828"
        elif q_val<15: d,c = "Low Q","#e65100"
        elif q_val<25: d,c = "Moderate Q","#f9a825"
        elif q_val<40: d,c = "High Q","#2e7d32"
        else: d,c = "Very High Q","#1b5e20"
        
        ax.text(0, -0.65, d, ha='center', va='center', fontsize=11, color=c, fontweight='bold')
        if peak_freq and bw_val: ax.text(0, -0.95, f"f\u2080/BW = {peak_freq:.2f}/{bw_val:.3f}", ha='center', fontsize=9, color='gray')

    def update_polar_ui(self, al=None, vl=None, pol_min=-30):
        if al is not None and vl is not None:
            self._last_polar_al = al
            self._last_polar_vl = vl
        else:
            al = getattr(self, '_last_polar_al', None)
            vl = getattr(self, '_last_polar_vl', None)
            
        self.ax_p.clear(); self.ax_p.set_theta_zero_location("N"); self.ax_p.set_theta_direction(-1)
        
        # Plot Measured Data
        if al is not None and vl is not None and len(al) > 0 and len(vl) > 0:
            mx = max(vl) or 1
            # Clip measured values to min bounds so they meet at the center point instead of looping
            norm = [max(pol_min, 20*np.log10((v/mx) + 1e-18)) for v in vl]
            self.ax_p.plot(al, norm, color='red', lw=2, label="Measured", zorder=5)
        
        # Plot Overlays (Historical Scans)
        for idx, (oa, on) in enumerate(self._polar_overlays): 
            on_clipped = [max(pol_min, val) for val in on]
            self.ax_p.plot(oa, on_clipped, color='gray', lw=1, alpha=0.5, label=f"Overlay {idx+1}")
        
        # Plot Theoretical Prediction if enabled
        if self.pred_show.get():
            # Generate ultra-high resolution angles (36000 points) to guarantee sampling of exact mathematical nulls
            pred_angles = np.linspace(-np.pi/2, np.pi/2, 36000)
            pred_db = self._calculate_theoretical_pattern(pred_angles)
            if pred_db is not None:
                # Clip theoretical predictions so deep nulls resolve precisely to the graph origin
                pred_db = np.clip(pred_db, pol_min, 0)
                
                # Removed the artificial concatenation that was drawing horizontal lines to the origin
                self.ax_p.plot(pred_angles, pred_db, color='#0288d1', ls='--', lw=2, label="Theoretical", zorder=10)
        
        self.ax_p.set_ylim(pol_min, 0)
        self.ax_p.set_rorigin(pol_min) # Rigidly enforce origin stop bounds
        self.ax_p.set_title("Polar Radiation Pattern")
        
        # Handle legend interactive state
        h, l = self.ax_p.get_legend_handles_labels()
        if h:
            leg = self.ax_p.legend(h, l, loc='upper right', fontsize=8)
            self.ax_p._master_handles = h; self.ax_p._master_labels = l; self.ax_p._leg_loc = 'upper right'; self.ax_p._leg_fs = 8
            self._make_legend_interactive(leg, h, self.ax_p)
            
        self._make_labels_editable(self.ax_p)
        self.canvas_p.draw()

    # ------------------------------------------------------------------
    # Save All & Load
    # ------------------------------------------------------------------
    def save_aas(self):
        """Overwrites the currently loaded .aas file, or prompts for a new location if none exists."""
        if not self._current_aas_file:
            self.save_as_aas()
            return
        self._write_aas_state(self._current_aas_file)
        self.log(f"Saved to: {os.path.basename(self._current_aas_file)}")
        self._flash_file_btn()
        
    def save_as_aas(self):
        """Prompts for a new location and saves a fresh .aas file."""
        filepath = filedialog.asksaveasfilename(defaultextension=".aas", filetypes=[("Air Acoustics Save", "*.aas")])
        if not filepath: return
        self._current_aas_file = filepath
        self._write_aas_state(self._current_aas_file)
        self.log(f"Saved As: {os.path.basename(self._current_aas_file)}")
        self._flash_file_btn()
        
    def _write_aas_state(self, filepath):
        try:
            state = {
                'settings': self._get_current_settings_dict(), 'dash': self._get_dash_state(),
                'last_burst_t': self.last_burst_t, 'last_burst_tx': self.last_burst_tx, 'last_burst_mic': self.last_burst_mic,
                '_last_burst_pre_list': self._last_burst_pre_list, 'last_sweep_data': self.last_sweep_data,
                'last_polar_data': self.last_polar_data, 'last_adv_raw': self.last_adv_raw, 'last_cwt_raw': self.last_cwt_raw,
                '_polar_overlays': getattr(self, '_polar_overlays', []), 'imp_data': getattr(self, 'imp_data', {}), 'burst_kwargs': self._last_burst_kwargs,
                'sw_bw_kwargs': self._last_sw_bw_kwargs, 'polar_kwargs': self._last_polar_kwargs,
                'adv_kwargs': self._last_adv_kwargs, 'cwt_kwargs': self._last_cwt_kwargs
            }
            with gzip.open(filepath, 'wb') as f: pickle.dump(state, f)
            self._is_dirty = False
        except Exception as e:
            self.log(f"Save err: {e}")
            messagebox.showerror("Save Error", f"Could not save file.\n{e}")

    def _flash_file_btn(self):
        orig_color = self.file_btn.cget("text_color")
        self.file_btn.configure(text_color="#00E676", text="✓ SAVED")
        self.after(1500, lambda: self.file_btn.configure(text_color=orig_color, text="📁 File"))

    def _export_workflow(self, title, save_plots=False, save_csvs=False, save_aas=False):
        dialog = ctk.CTkInputDialog(text="Folder name (blank = timestamp):", title=title)
        name = dialog.get_input()
        if name is None: return
        ts = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        if not name.strip(): name = f"Acoustics_{ts}"
        else: name = "".join(c for c in name if c.isalnum() or c in ' _-').rstrip()
        parent = filedialog.askdirectory(title=f"Select Destination for {title}:")
        if not parent: return
        
        sd = pathlib.Path(parent) / name; sd.mkdir(parents=True, exist_ok=True)
        
        # Get a comma separated list of loaded impedance files (if any)
        imp_files = ", ".join(self.imp_data.keys()) if hasattr(self, 'imp_data') and self.imp_data else "None"
        
        # FIX: Expanded the Lab Report to include all hardware settings for total replicability
        with open(sd / "Full_Lab_Report.txt", 'w', encoding='utf-8') as f:
            f.write(f"Air Acoustics Suite 1.0 — Lab Report\n{'='*50}\nScan: {name}\nTime: {ts}\n\n"
                    
                    f"--- CALIBRATION ---\n"
                    f"Temp: {self.temp_entry.get()} °C  |  Humidity: {self.humidity_entry.get()} %RH\n"
                    f"Mic Sens: {self.mic_sens.get()} mV/Pa  |  Gain: {self.module_gain.get()} dB  |  Eff Sens: {self._effective_sens_v_pa()*1000:.2f} mV/Pa\n"
                    f"Ref Distance: {self.ref_dist_entry.get()} cm  |  Override ToF: {self.ref_dist_lock_var.get()}\n"
                    f"Calibrated Noise Floor: {self._calibrated_noise_rms:.6f} V RMS\n\n"
                    
                    f"--- BURST ANALYSIS ---\n"
                    f"[Settings] Mode: {self.burst_fg_mode.get()} | Wave: {self.burst_wave.get()} | Drive: {self.burst_f.get()} kHz, {self.burst_voltage.get()} V, {self.burst_cycles.get()} Cycles\n"
                    f"[Settings] Scope: {self.burst_acq.get()} ({self.burst_avg_n.get()} avgs) | FG ON Time: {self.burst_capture_time.get()}s\n"
                    f"[Results]  Vpp: {self.dash_vpp.cget('text')}  |  Pa: {self.dash_pa.cget('text')}\n"
                    f"[Results]  SPL: {self.dash_spl.cget('text')}  |  {self.dash_sl.cget('text')}\n"
                    f"[Results]  SNR: {self.dash_snr.cget('text')}  |  ToF Dist: {self.dash_dist.cget('text')}\n"
                    f"[Results]  {self.dash_thd.cget('text')}  |  {self.dash_tau.cget('text')}\n\n"
                    
                    f"--- RESONANCE SWEEP ---\n"
                    f"[Settings] Wave: {self.sweep_wave.get()} | Drive: {self.sweep_voltage.get()} V | Meas: {self.sweep_meas.get()} | Dwell: {self.sweep_dwell.get()}s\n"
                    f"[Settings] Range: {self.start_f.get()} to {self.end_f.get()} kHz | Step: {self.step_f.get()} kHz ({self.sweep_spacing.get()})\n"
                    f"[Results]  Peak: {self.dash_peak_f.cget('text')}  |  BW: {self.dash_bw.cget('text')}  |  Q: {self.dash_q.cget('text')}\n\n"
                    
                    f"--- POLAR PLOT ---\n"
                    f"[Settings] Wave: {self.polar_wave.get()} | Drive: {self.pol_f.get()} kHz, {self.polar_voltage.get()} V | Dwell: {self.pol_dwell.get()}s\n"
                    f"[Settings] Range: {self.pol_start.get()}° to {self.pol_end.get()}° | Step: {self.pol_step.get()}° ({self.pol_dir.get()})\n"
                    f"[Theoretical] Shape: {self.pred_geom.get()} | Dimension: {self.pred_dim.get()} mm | Mode: ({self.pred_mode_n.get()},{self.pred_mode_m.get()})\n"
                    f"[Results]  -3dB: {self.dash_bw3.cget('text')}  |  -6dB: {self.dash_bw6.cget('text')}\n\n"
                    
                    f"--- ADVANCED TIMING & IMPEDANCE ---\n"
                    f"[Wavelet]  Drive: {self.cwt_f.get()} kHz, {self.cwt_voltage.get()} V, {self.cwt_cycles.get()} Cycles ({self.cwt_wave.get()})\n"
                    f"[STFT]     Drive: {self.adv_f.get()} kHz, {self.adv_voltage.get()} V, {self.adv_cycles.get()} Cycles ({self.adv_wave.get()})\n"
                    f"[Impedance] Imported CSVs: {imp_files}\n"
                    f"{'='*50}\n")
                    
        if save_plots:
            try:
                plots_to_save = [
                    (self.last_burst_t is not None, self.fig_b, 'Plot_Burst', (12, 10)),
                    (self.last_sweep_data is not None, self.fig_sw, 'Plot_Resonance', (16, 6)),
                    (self.last_polar_data is not None, self.fig_p, 'Plot_Polar', (8, 8)),
                    (self.last_adv_raw is not None, self.fig_adv, 'Plot_STFT', (12, 6)),
                    (self.last_cwt_raw is not None, self.fig_cwt, 'Plot_Wavelet', (12, 6)),
                    (bool(getattr(self, 'imp_data', {})), self.fig_imp, 'Plot_Impedance', (12, 6))
                ]
                for has_data, fig, fn, target_size in plots_to_save:
                    if has_data and fig:
                        orig_size = fig.get_size_inches()
                        fig.set_size_inches(*target_size)
                        fig.tight_layout()
                        fig.savefig(sd / f"{fn}.png", dpi=200, bbox_inches='tight')
                        fig.set_size_inches(*orig_size)
                        fig.tight_layout()
                        fig.canvas.draw_idle()
            except Exception as e: self.log(f"Plot export err: {e}")
            
        if save_csvs:
            try:
                if self.last_burst_t is not None: np.savetxt(sd/"Data_Burst.csv", np.column_stack((self.last_burst_t, self.last_burst_tx, self.last_burst_mic)), delimiter=",", header="Time_s,TX_V,RX_V", comments='')
                if self.last_sweep_data is not None: np.savetxt(sd/"Data_Sweep.csv", self.last_sweep_data, delimiter=",", header="Freq_kHz,V_rms,Pa_rms,SPL_dB", comments='')
                if self.last_polar_data is not None: np.savetxt(sd/"Data_Polar.csv", self.last_polar_data, delimiter=",", header="Angle_rad,Mag_dBnorm", comments='')
                if hasattr(self, 'imp_data') and self.imp_data:
                    for imp_name, (f_data, z_data, p_data) in self.imp_data.items():
                        np.savetxt(sd / f"Impedance_{imp_name}.csv", np.column_stack((f_data, z_data, p_data)), delimiter=",", header="Frequency_Hz,Z_Ohm,Phase_deg", comments='')
            except Exception as e: self.log(f"CSV export err: {e}")
            
        if save_aas:
            self._write_aas_state(sd / f"{name}.aas")
            self._current_aas_file = str(sd / f"{name}.aas")

        self.log(f"{title} Complete: {name}")
        messagebox.showinfo("Export Successful", f"Successfully exported to:\n{sd}")

    def load_aas_file_dialog(self):
        if not self.check_dirty_and_prompt("loading a new file"): return
        filepath = filedialog.askopenfilename(filetypes=[("Air Acoustics Save", "*.aas")])
        if filepath: self.load_aas_file(filepath)

    def load_aas_file(self, filepath):
        try:
            with gzip.open(filepath, 'rb') as f: state = pickle.load(f)
            if 'settings' in state: self._apply_settings_dict(state['settings'])
            if 'dash' in state: self._set_dash_state(state['dash'])
            self.last_burst_t = state.get('last_burst_t'); self.last_burst_tx = state.get('last_burst_tx'); self.last_burst_mic = state.get('last_burst_mic')
            self._last_burst_pre_list = state.get('_last_burst_pre_list'); self.last_sweep_data = state.get('last_sweep_data')
            self.last_polar_data = state.get('last_polar_data'); self.last_adv_raw = state.get('last_adv_raw')
            self.last_cwt_raw = state.get('last_cwt_raw'); self._polar_overlays = state.get('_polar_overlays', [])
            if 'imp_data' in state:
                self.imp_data = state['imp_data']
                self.update_imp_listbox(); self.update_imp_plot()
            if state.get('burst_kwargs'): self.update_burst_ui(**state['burst_kwargs'])
            if state.get('sw_bw_kwargs') and self.last_sweep_data is not None:
                sd = self.last_sweep_data; yaxis = self.sweep_yaxis.get()
                y_idx = {"SPL (dB)": 3, "Pa RMS": 2, "V RMS": 1}.get(yaxis, 3)
                self.update_sw_plot(sd[:, 0], sd[:, y_idx], yaxis); self.update_sw_bw_plot(**state['sw_bw_kwargs'])
            if state.get('polar_kwargs'): self.update_polar_ui(**state['polar_kwargs'])
            if state.get('adv_kwargs'): self.update_adv_ui(**state['adv_kwargs'])
            if state.get('cwt_kwargs'): self.update_cwt_ui(**state['cwt_kwargs'])
            self.log(f"Successfully loaded interactive data from: {os.path.basename(filepath)}")
            self._current_aas_file = filepath
            self._is_dirty = False
        except Exception as e:
            self.log(f"Failed to load .aas file: {e}"); messagebox.showerror("Load Error", f"Could not load file.\n{e}")

    def save_plot_png(self, fig):
        p = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG","*.png")])
        if p: fig.savefig(p, dpi=150)

if __name__ == "__main__":
    app = AirAcousticsSuite()
    app.mainloop()