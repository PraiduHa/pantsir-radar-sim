import sys
import faulthandler
import traceback
from datetime import datetime

try:
    _crash_fh = open("suo_crash.log", "a", encoding="utf-8")
    faulthandler.enable(file=_crash_fh, all_threads=True)
except Exception:
    pass


def _log_py_err(context, exc):
    try:
        ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        with open("suo_crash.log", "a", encoding="utf-8") as fh:
            fh.write(f"[{ts}] {context}: {exc}\n{traceback.format_exc()}\n")
    except Exception:
        pass


import math
import random
import os
import tempfile
import io
import wave
import numpy as np
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QLabel, QPushButton, QSlider, QComboBox, QTabWidget, QFrame, QTableWidget,
    QTableWidgetItem, QHeaderView, QTextEdit, QSpinBox, QProgressBar, QListWidget,
    QListWidgetItem
)
from PyQt6.QtCore import QTimer, Qt, QPointF, QRectF, QUrl
from PyQt6.QtGui import QImage, QPixmap, QPainter, QColor, QPen, QFont, QBrush, QPolygonF

try:
    from PyQt6.QtMultimedia import QSoundEffect
    _HAS_QSOUND = True
except Exception:
    QSoundEffect = None
    _HAS_QSOUND = False

C = 3e8
MAX_RANGE_KM = 36.0
COMBAT_EXTRA_OUT_KM = 4.0      # Залёт за пределы радара на +4 км (до 40 км в боевом режиме)
SENSOR_W = 96
SENSOR_H = 72
COAST_DURATION_SEC = 4.0
FADE_DURATION_SEC = 1.5
NOTCH_VR_MS = 18.0

# Параметры вооружения и перегрева
SAM_MAX_AMMO = 12
SAM_FIRE_INTERVAL = 2.0        # 30 пусков/мин
SAM_MAX_RANGE_KM = 20.0
SAM_SPEED_MS = 1300.0
SAM_FLIGHT_TIME_SEC = 30.0

GUN_MAX_AMMO = 1404
GUN_BELT_SIZE = 351
GUN_RPM = 1250.0
GUN_SHOT_INTERVAL = 60.0 / GUN_RPM  # ~0.048 с
GUN_MUZZLE_VEL_MS = 960.0
GUN_DEFAULT_RANGE_LIMIT_KM = 5.0

TEMP_AMBIENT = 20.0
TEMP_PER_SHOT = 3.0
TEMP_COOL_K = 0.08
TEMP_WARN = 350.0
TEMP_CRIT = 680.0

ENEMY_TEMPLATES = {
    "Су-30СМ (Ударный)": ("fighter", 5.0, ["Х-31П (ПРР)", "Х-59МК (УР В-П)"]),
    "F-16C (SEAD / ПРР)": ("fighter", 3.3, ["AGM-88B HARM (ПРР)", "AGM-65G Maverick"]),
    "Rafale (Многоцелевой)": ("fighter", 3.5, ["AASM Hammer-250", "SCALP-EG / АСП"]),
    "БПЛА-разведчик": ("uav", 0.65, []),
    "БПЛА-ударный": ("uav", 0.80, ["Управляемый боеприпас БПЛА"]),
}


def ang_diff_deg(a, b):
    return (a - b + 180.0) % 360.0 - 180.0


def beam_crossed_az(prev_az, curr_az, target_az, margin_deg=4.5):
    d_prev = ang_diff_deg(target_az, prev_az)
    d_curr = ang_diff_deg(target_az, curr_az)
    step = ang_diff_deg(curr_az, prev_az)
    if abs(d_curr) > max(margin_deg + 2.0, abs(step) + 1.5):
        return False
    if abs(step) > 90.0:
        return abs(d_curr) <= margin_deg
    if step >= 0.0:
        return (-margin_deg <= d_prev <= margin_deg) or (d_prev < 0.0 and d_curr >= 0.0)
    else:
        return (-margin_deg <= d_prev <= margin_deg) or (d_prev > 0.0 and d_curr <= 0.0)


class SoundEngine:
    """Генератор приглушённых звуков изнутри машины и тревоги с поддержкой нескольких бэкендов."""
    def __init__(self, parent=None):
        self.parent = parent
        self.enabled = True
        self.volume = 0.80
        self._backend = None
        self._tmp_dir = None
        self._gun_effect = None
        self._alarm_effect = None
        self._sam_effect = None
        self._jam_effect = None
        self._gun_wav_path = None
        self._alarm_wav_path = None
        self._sam_wav_path = None
        self._jam_wav_path = None
        self._pygame_sounds = {}
        self._last_gun_ts = -10.0
        self._last_alarm_ts = -10.0
        self._init_audio()

    def _write_wav_file(self, filename, samples_f32, sr=22050):
        pcm = np.clip(samples_f32 * 32767.0, -32768, 32767).astype(np.int16)
        path = os.path.join(self._tmp_dir, filename)
        with wave.open(path, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sr)
            wf.writeframes(pcm.tobytes())
        return path

    def _init_audio(self):
        try:
            self._tmp_dir = tempfile.mkdtemp(prefix="pantsir_sfx_")
            sr = 22050

            # Приглушённый выстрел автопушки 2А38М изнутри боевого отделения (низкочастотный бухающий удар)
            t_gun = np.linspace(0, 0.065, int(sr * 0.065), endpoint=False)
            env_g = np.exp(-t_gun * 52.0)
            thump = np.sin(2 * np.pi * 72.0 * t_gun) * 0.72 + np.sin(2 * np.pi * 128.0 * t_gun) * 0.35
            noise_g = np.random.normal(0.0, 0.35, len(t_gun))
            kernel = np.ones(18) / 18.0
            noise_lp = np.convolve(noise_g, kernel, mode="same")
            gun_sig = (thump + noise_lp) * env_g * 0.75
            self._gun_wav_path = self._write_wav_file("gun_muffled.wav", gun_sig, sr)

            # Тревожный сигнал при засечении ответного пуска по «Панцирю»
            t_al = np.linspace(0, 0.48, int(sr * 0.48), endpoint=False)
            tone1 = np.sin(2 * np.pi * 920.0 * t_al) * ((t_al < 0.20) & (t_al >= 0.01))
            tone2 = np.sin(2 * np.pi * 1240.0 * t_al) * ((t_al >= 0.23) & (t_al < 0.44))
            alarm_sig = (tone1 + tone2) * 0.70
            self._alarm_wav_path = self._write_wav_file("threat_alarm.wav", alarm_sig, sr)

            # Пуск ЗУР 95Я6
            t_sam = np.linspace(0, 0.26, int(sr * 0.26), endpoint=False)
            env_s = np.exp(-t_sam * 13.0)
            sam_sig = (
                np.sin(2 * np.pi * 92.0 * t_sam) * 0.6 +
                np.convolve(np.random.normal(0, 0.4, len(t_sam)), np.ones(12) / 12.0, mode="same")
            ) * env_s * 0.65
            self._sam_wav_path = self._write_wav_file("sam_launch.wav", sam_sig, sr)

            # Клин стволов
            t_jm = np.linspace(0, 0.18, int(sr * 0.18), endpoint=False)
            jm_sig = (np.sin(2 * np.pi * 290.0 * t_jm) + np.sin(2 * np.pi * 460.0 * t_jm)) * np.exp(-t_jm * 24.0) * 0.65
            self._jam_wav_path = self._write_wav_file("gun_jam.wav", jm_sig, sr)

            # Пробуем QtMultimedia QSoundEffect (не обрывает звуки так агрессивно, как winsound SND_ASYNC)
            if _HAS_QSOUND and QSoundEffect is not None:
                try:
                    ge = QSoundEffect(self.parent)
                    ge.setSource(QUrl.fromLocalFile(self._gun_wav_path))
                    ge.setVolume(self.volume)

                    ae = QSoundEffect(self.parent)
                    ae.setSource(QUrl.fromLocalFile(self._alarm_wav_path))
                    ae.setVolume(min(1.0, self.volume * 1.05))

                    se = QSoundEffect(self.parent)
                    se.setSource(QUrl.fromLocalFile(self._sam_wav_path))
                    se.setVolume(self.volume)

                    je = QSoundEffect(self.parent)
                    je.setSource(QUrl.fromLocalFile(self._jam_wav_path))
                    je.setVolume(self.volume)

                    self._gun_effect = ge
                    self._alarm_effect = ae
                    self._sam_effect = se
                    self._jam_effect = je
                    self._backend = "qsound"
                    return
                except Exception:
                    pass

            # Запасной вариант: pygame.mixer
            try:
                import pygame
                if not pygame.mixer.get_init():
                    pygame.mixer.init(frequency=sr, size=-16, channels=1, buffer=512)
                self._pygame_sounds["gun"] = pygame.mixer.Sound(self._gun_wav_path)
                self._pygame_sounds["alarm"] = pygame.mixer.Sound(self._alarm_wav_path)
                self._pygame_sounds["sam"] = pygame.mixer.Sound(self._sam_wav_path)
                self._pygame_sounds["jam"] = pygame.mixer.Sound(self._jam_wav_path)
                self._backend = "pygame"
                return
            except Exception:
                pass

            # Запасной вариант для Windows: winsound
            try:
                import winsound  # noqa: F401
                self._backend = "winsound"
            except Exception:
                self._backend = None
        except Exception as exc:
            _log_py_err("SoundEngine._init_audio", exc)
            self._backend = None

    def set_volume(self, vol_0_to_1):
        self.volume = max(0.0, min(1.0, float(vol_0_to_1)))
        try:
            if self._backend == "qsound":
                for eff, mult in (
                    (self._gun_effect, 1.0),
                    (self._alarm_effect, 1.05),
                    (self._sam_effect, 1.0),
                    (self._jam_effect, 1.0),
                ):
                    if eff is not None:
                        eff.setVolume(min(1.0, self.volume * mult))
            elif self._backend == "pygame":
                for snd in self._pygame_sounds.values():
                    snd.set_volume(self.volume)
        except Exception:
            pass

    def _trigger_sound(self, key, effect_obj, wav_path, min_gap=0.06, now_sec=None):
        if not self.enabled or self.volume <= 0.001 or not self._backend:
            return
        try:
            if self._backend == "qsound" and effect_obj is not None:
                if key == "gun" and now_sec is not None and (now_sec - self._last_gun_ts) < min_gap:
                    return
                if key == "gun" and now_sec is not None:
                    self._last_gun_ts = now_sec
                if not effect_obj.isPlaying():
                    effect_obj.play()
                elif key == "alarm":
                    effect_obj.stop()
                    effect_obj.play()
            elif self._backend == "pygame" and key in self._pygame_sounds:
                if key == "gun" and now_sec is not None and (now_sec - self._last_gun_ts) < min_gap:
                    return
                if key == "gun" and now_sec is not None:
                    self._last_gun_ts = now_sec
                ch = pygame.mixer.find_channel(True) if "pygame" in sys.modules else None
                if ch is not None:
                    ch.play(self._pygame_sounds[key])
                else:
                    self._pygame_sounds[key].play()
            elif self._backend == "winsound" and wav_path:
                import winsound
                if key == "gun":
                    if now_sec is not None and (now_sec - self._last_gun_ts) < 0.085:
                        return
                    if now_sec is not None:
                        self._last_gun_ts = now_sec
                    winsound.PlaySound(wav_path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NOSTOP)
                else:
                    winsound.PlaySound(wav_path, winsound.SND_FILENAME | winsound.SND_ASYNC)
        except Exception:
            pass

    def play_gun_shot(self, now_sec=None):
        self._trigger_sound("gun", self._gun_effect, self._gun_wav_path, min_gap=0.075, now_sec=now_sec)

    def play_sam_launch(self):
        self._trigger_sound("sam", self._sam_effect, self._sam_wav_path, min_gap=0.1)

    def play_jam(self):
        self._trigger_sound("jam", self._jam_effect, self._jam_wav_path, min_gap=0.1)

    def play_alarm(self, now_sec):
        if now_sec - self._last_alarm_ts < 0.65:
            return
        self._last_alarm_ts = now_sec
        self._trigger_sound("alarm", self._alarm_effect, self._alarm_wav_path, min_gap=0.6)


class SimTarget:
    """Воздушная цель или подлетающий вражеский боеприпас."""
    def __init__(
        self, tid, name, kind, x_km, y_km, alt_km, vx_ms, vy_ms,
        rcs=3.0, ordnance_list=None, is_munitions=False, parent_id=None, max_out_km=None
    ):
        self.id = tid
        self.name = name
        self.kind = kind          # 'fighter', 'uav', 'liner', 'missile'
        self.x = float(x_km)
        self.y = float(y_km)
        self.alt = float(alt_km)
        self.vx = float(vx_ms)
        self.vy = float(vy_ms)
        self.rcs = float(rcs)
        self.is_munitions = bool(is_munitions)
        self.parent_id = parent_id
        self.max_out_km = float(MAX_RANGE_KM * 0.94 if max_out_km is None else max_out_km)

        if ordnance_list is not None:
            self.ordnance = list(ordnance_list)
        else:
            self.ordnance = self._default_ordnance_for_name(name, kind)

        self.hp = 100.0 if kind == "fighter" else (220.0 if kind == "liner" else (45.0 if kind == "uav" else 20.0))
        self.alive = True
        self.dying_timer = 0.0
        self.explosion_heat = 0.0

        self.detected = True
        self.in_sector = True
        self.clutter_notched = False
        self.blip_alpha = 1.0

        self.is_coasting = False
        self.coast_elapsed = 0.0
        self.fade_elapsed = 0.0
        self.pred_x = float(x_km)
        self.pred_y = float(y_km)
        self.pred_vx = float(vx_ms)
        self.pred_vy = float(vy_ms)
        self.track_visible = True

        self.radar_x = float(x_km)
        self.radar_y = float(y_km)
        self.radar_alt = float(alt_km)
        self.radar_vx = float(vx_ms)
        self.radar_vy = float(vy_ms)
        self.radar_speed = math.hypot(vx_ms, vy_ms)
        self.radar_vr = 0.0
        self.radar_fd = 0.0
        self.radar_extrap_x = float(x_km)
        self.radar_extrap_y = float(y_km)
        self.radar_update_flash = 0.0
        self.has_radar_fix = True

        self.evasion_timer = 0.0
        self.evasion_turn_rate = 0.0
        self.evasion_alt_rate = 0.0
        self.jamming_boost = 0.0
        self.jamming_timer = 0.0
        self.attack_cooldown = random.uniform(4.5, 9.5)
        self.under_fire_react_cd = 0.0

    @staticmethod
    def _default_ordnance_for_name(name, kind):
        if "ударный" in name.lower():
            return ["Управляемый боеприпас БПЛА"]
        if kind != "fighter":
            return []
        low = name.lower()
        if "су-30" in low:
            return ["Х-31П (ПРР)", "Х-59МК (УР В-П)"]
        if "f-16" in low:
            return ["AGM-88B HARM (ПРР)", "AGM-65G Maverick"]
        if "rafale" in low:
            return ["AASM Hammer-250", "SCALP-EG / АСП"]
        return ["УР воздух-поверхность"]

    def trigger_defensive_maneuver(self, force_notch=False):
        if self.is_munitions or not self.alive:
            return
        spd = max(80.0, self.speed())
        _, az_deg, _ = self.polar()
        if force_notch:
            perp_deg = (az_deg + random.choice([-90.0, 90.0])) % 360.0
            rad = math.radians(perp_deg)
            self.vx = spd * math.sin(rad)
            self.vy = spd * math.cos(rad)
            self.evasion_timer = 2.8
            self.evasion_turn_rate = 0.0
        else:
            self.evasion_timer = random.uniform(2.2, 4.0)
            self.evasion_turn_rate = random.choice([-1.0, 1.0]) * random.uniform(16.0, 28.0)
            self.evasion_alt_rate = random.choice([-1.0, 1.0]) * random.uniform(0.08, 0.18)
        if self.kind == "fighter" and random.random() < 0.55:
            self.jamming_timer = random.uniform(2.5, 4.5)
            self.jamming_boost = random.uniform(0.18, 0.34)

    def step(self, dt):
        if not self.alive:
            if self.dying_timer > 0.0:
                self.dying_timer = max(0.0, self.dying_timer - dt * 0.22)
                self.explosion_heat = max(0.0, self.dying_timer / 2.2)
            self.x += (self.vx / 1000.0) * dt * 0.35
            self.y += (self.vy / 1000.0) * dt * 0.35
            self.alt = max(0.0, self.alt - 0.06 * dt)
            return

        if self.is_munitions:
            r_horiz = math.hypot(self.x, self.y)
            r_3d = math.hypot(r_horiz, self.alt)
            spd = max(260.0, self.speed())
            if r_3d > 0.02:
                self.vx = -(self.x / r_3d) * spd
                self.vy = -(self.y / r_3d) * spd
                vz = -(self.alt / r_3d) * spd
                self.x += (self.vx / 1000.0) * dt
                self.y += (self.vy / 1000.0) * dt
                self.alt = max(0.0, self.alt + (vz / 1000.0) * dt)
            return

        if self.jamming_timer > 0.0:
            self.jamming_timer = max(0.0, self.jamming_timer - dt * 0.22)
            if self.jamming_timer <= 0.0:
                self.jamming_boost = 0.0

        if self.under_fire_react_cd > 0.0:
            self.under_fire_react_cd = max(0.0, self.under_fire_react_cd - dt * 0.22)

        if self.evasion_timer > 0.0:
            self.evasion_timer = max(0.0, self.evasion_timer - dt * 0.22)
            hdg = math.radians(self.heading_deg() + self.evasion_turn_rate * dt)
            spd = self.speed()
            self.vx = spd * math.sin(hdg)
            self.vy = spd * math.cos(hdg)
            self.alt = max(0.4, min(11.5, self.alt + self.evasion_alt_rate * dt))

        self.x += (self.vx / 1000.0) * dt
        self.y += (self.vy / 1000.0) * dt
        dist = math.hypot(self.x, self.y)
        limit_km = self.max_out_km
        if dist > limit_km:
            if dist > 1e-5:
                nx, ny = self.x / dist, self.y / dist
                self.x = nx * (limit_km - 0.15)
                self.y = ny * (limit_km - 0.15)
                # Разворот ближе к центру или по касательной с уводом вглубь/наружу
                turn_rad = math.radians(random.uniform(135.0, 225.0))
                spd = max(60.0, self.speed())
                cur_ang = math.atan2(self.vx, self.vy)
                new_ang = cur_ang + turn_rad
                self.vx = spd * math.sin(new_ang)
                self.vy = spd * math.cos(new_ang)

    def kill_with_explosion(self):
        self.alive = False
        self.dying_timer = 2.2
        self.explosion_heat = 1.0
        self.detected = False
        self.track_visible = False
        self.is_coasting = False
        self.blip_alpha = 0.0

    def update_track_coasting(self, has_live_track, sim_dt, dt_real):
        if not self.alive:
            self.track_visible = False
            self.blip_alpha = 0.0
            return
        if has_live_track:
            self.is_coasting = False
            self.coast_elapsed = 0.0
            self.fade_elapsed = 0.0
            self.blip_alpha = 1.0
            self.track_visible = True
            self.pred_x = self.x
            self.pred_y = self.y
            self.pred_vx = self.vx
            self.pred_vy = self.vy
            return

        if not self.is_coasting and self.track_visible:
            self.is_coasting = True
            self.coast_elapsed = 0.0
            self.fade_elapsed = 0.0
            self.blip_alpha = 1.0
            self.pred_x = self.x
            self.pred_y = self.y
            self.pred_vx = self.vx
            self.pred_vy = self.vy

        if self.is_coasting:
            if self.coast_elapsed < COAST_DURATION_SEC:
                self.coast_elapsed += dt_real
                self.pred_x += (self.pred_vx / 1000.0) * sim_dt
                self.pred_y += (self.pred_vy / 1000.0) * sim_dt
                self.blip_alpha = 0.85
                self.track_visible = True
            else:
                self.fade_elapsed += dt_real
                self.pred_x += (self.pred_vx / 1000.0) * sim_dt
                self.pred_y += (self.pred_vy / 1000.0) * sim_dt
                ratio = min(1.0, self.fade_elapsed / FADE_DURATION_SEC)
                self.blip_alpha = max(0.0, 0.85 * (1.0 - ratio))
                if ratio >= 1.0:
                    self.track_visible = False
                    self.is_coasting = False

    def refresh_from_radar(self, f0_ghz):
        self.radar_x = self.x
        self.radar_y = self.y
        self.radar_alt = self.alt
        self.radar_vx = self.vx
        self.radar_vy = self.vy
        self.radar_speed = self.speed()
        self.radar_vr = self.radial_vel()
        self.radar_fd = self.doppler_khz(f0_ghz)
        self.radar_extrap_x = self.x
        self.radar_extrap_y = self.y
        self.radar_update_flash = 1.0
        self.has_radar_fix = True

    def step_radar_extrapolation(self, sim_dt, dt_real):
        if self.radar_update_flash > 0.0:
            self.radar_update_flash = max(0.0, self.radar_update_flash - dt_real * 2.2)
        if sim_dt > 0.0:
            self.radar_extrap_x += (self.radar_vx / 1000.0) * sim_dt
            self.radar_extrap_y += (self.radar_vy / 1000.0) * sim_dt

    def swept_polar(self):
        r_horiz = math.hypot(self.radar_extrap_x, self.radar_extrap_y)
        r_slant = math.hypot(r_horiz, self.radar_alt)
        az = math.degrees(math.atan2(self.radar_extrap_x, self.radar_extrap_y)) % 360.0
        el = math.degrees(math.atan2(self.radar_alt, max(0.05, r_horiz)))
        return r_slant, az, el

    def swept_heading_deg(self):
        return math.degrees(math.atan2(self.radar_vx, self.radar_vy)) % 360.0

    def display_xy(self):
        if self.is_coasting:
            return self.pred_x, self.pred_y
        return self.x, self.y

    def display_polar(self):
        dx, dy = self.display_xy()
        r_horiz = math.hypot(dx, dy)
        r_slant = math.hypot(r_horiz, self.alt)
        az = math.degrees(math.atan2(dx, dy)) % 360.0
        el = math.degrees(math.atan2(self.alt, max(0.05, r_horiz)))
        return r_slant, az, el

    def polar(self):
        r_horiz = math.hypot(self.x, self.y)
        r_slant = math.hypot(r_horiz, self.alt)
        az = math.degrees(math.atan2(self.x, self.y)) % 360.0
        el = math.degrees(math.atan2(self.alt, max(0.05, r_horiz)))
        return r_slant, az, el

    def speed(self):
        return math.hypot(self.vx, self.vy)

    def radial_vel(self):
        r_m = math.hypot(self.x, self.y) * 1000.0
        if r_m < 1.0:
            return 0.0
        return -(self.x * 1000.0 * self.vx + self.y * 1000.0 * self.vy) / r_m

    def doppler_khz(self, f0_ghz):
        vr = self.radial_vel()
        return (2.0 * vr * (f0_ghz * 1e9) / C) / 1000.0

    def heading_deg(self):
        vx, vy = (self.pred_vx, self.pred_vy) if self.is_coasting else (self.vx, self.vy)
        return math.degrees(math.atan2(vx, vy)) % 360.0


class ActiveSamProjectile:
    def __init__(self, mid, target_id, channel_mode, is_directed, start_az, start_el):
        self.id = mid
        self.target_id = target_id
        self.channel_mode = channel_mode
        self.is_directed = is_directed
        self.x = 0.0
        self.y = 0.0
        self.alt = 0.01
        self.az = start_az
        self.el = start_el
        self.flight_time = 0.0
        self.active = True
        self.status = "ПОЛЁТ"


class GunTracerBurst:
    def __init__(self, start_az, start_el, aim_az, aim_el, target_dist_km, hit_will_occur=False):
        self.start_az = start_az
        self.start_el = start_el
        self.aim_az = aim_az
        self.aim_el = aim_el
        self.target_dist_km = max(0.2, target_dist_km)
        self.travel_time_total = max(0.12, (self.target_dist_km * 1000.0) / GUN_MUZZLE_VEL_MS)
        self.elapsed = 0.0
        self.hit_will_occur = hit_will_occur
        self.active = True


class ThermalMonitorWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.setMinimumSize(440, 320)
        self.cam_az = 0.0
        self.cam_el = 15.0
        self.fov_deg = 24.0
        self.polarity = "WHOT"
        self.noise_level = 0.20
        self.auto_track = True
        self.zoom_x = 1
        self.zoom_glitch_sec = 0.0
        self.powered = True
        self.target = None
        self.active_sams = []
        self.active_tracers = []
        self.all_targets = []
        self.frame_pixmap = QPixmap(SENSOR_W, SENSOR_H)
        self.frame_pixmap.fill(QColor("#000000"))
        self._last_in_fov = False
        self._last_locked = True
        self._last_px = (SENSOR_W // 2, SENSOR_H // 2)
        self._last_size_px = 1

    def trigger_zoom_glitch(self, duration_sec=0.2):
        self.zoom_glitch_sec = max(self.zoom_glitch_sec, duration_sec)
        self.update()

    def tick_glitch(self, dt_real):
        if self.zoom_glitch_sec > 0.0:
            self.zoom_glitch_sec = max(0.0, self.zoom_glitch_sec - dt_real)

    def _project_angles(self, az_deg, el_deg, eff_fov):
        d_az = ang_diff_deg(az_deg, self.cam_az)
        d_el = el_deg - self.cam_el
        half_fov_x = eff_fov * 0.5
        half_fov_y = (eff_fov * (SENSOR_H / SENSOR_W)) * 0.5
        if abs(d_az) > half_fov_x or abs(d_el) > half_fov_y:
            return None
        px_x = int(round((0.5 + d_az / eff_fov) * (SENSOR_W - 1)))
        px_y = int(round((0.5 - d_el / (eff_fov * (SENSOR_H / SENSOR_W))) * (SENSOR_H - 1)))
        return px_x, px_y

    def update_scene(
        self, target, noise_level, cam_az, cam_el, notch_masked=False, powered=True,
        active_sams=None, active_tracers=None, all_targets=None
    ):
        self.powered = bool(powered)
        self.target = target
        self.noise_level = noise_level
        self.cam_az = cam_az
        self.cam_el = cam_el
        self.notch_masked = bool(notch_masked)
        self.active_sams = active_sams or []
        self.active_tracers = active_tracers or []
        self.all_targets = all_targets or ([] if target is None else [target])

        if not self.powered:
            self.frame_pixmap = QPixmap(SENSOR_W, SENSOR_H)
            self.frame_pixmap.fill(QColor("#000000"))
            self._last_in_fov = False
            self._last_locked = False
            self.update()
            return

        eff_fov = self.fov_deg / float(self.zoom_x)
        glitch_active = self.zoom_glitch_sec > 0.0

        y_grad = np.linspace(0.14, 0.28, SENSOR_H, dtype=np.float32)[:, None]
        bg = np.repeat(y_grad, SENSOR_W, axis=1)
        eff_noise = min(1.0, noise_level + (0.45 if glitch_active else 0.0))
        sensor_noise = np.random.normal(
            0.0, 0.025 + 0.16 * (eff_noise ** 1.15), size=(SENSOR_H, SENSOR_W)
        ).astype(np.float32)
        mat = np.clip(bg + sensor_noise, 0.0, 1.0)

        if glitch_active:
            for _ in range(4):
                bar_y = int(np.random.randint(0, SENSOR_H))
                y0 = max(0, bar_y - 1)
                y1 = min(SENSOR_H, bar_y + 1)
                mat[y0:y1, :] = np.clip(
                    np.random.uniform(0.05, 0.95, size=(y1 - y0, SENSOR_W)), 0.0, 1.0
                ).astype(np.float32)

        for t_item in self.all_targets:
            if (not t_item.alive) and t_item.dying_timer > 0.0:
                r_k, t_az, t_el = t_item.polar()
                pt = self._project_angles(t_az, t_el, eff_fov)
                if pt is not None:
                    ex_x, ex_y = pt
                    rad_px = max(2, int(round((12.0 * self.zoom_x * t_item.explosion_heat) / max(2.0, r_k * 0.45))))
                    rad_px = min(18, rad_px)
                    heat_val = min(0.99, 0.30 + 0.69 * t_item.explosion_heat)
                    for dy in range(-rad_px, rad_px + 1):
                        for dx in range(-rad_px, rad_px + 1):
                            if dx * dx + dy * dy <= rad_px * rad_px:
                                yy = ex_y + dy
                                xx = ex_x + dx
                                if 0 <= yy < SENSOR_H and 0 <= xx < SENSOR_W:
                                    falloff = 1.0 - (math.hypot(dx, dy) / max(1.0, rad_px)) * 0.45
                                    mat[yy, xx] = max(mat[yy, xx], heat_val * falloff)

        for sam in self.active_sams:
            if not sam.active:
                continue
            r_s = math.hypot(math.hypot(sam.x, sam.y), sam.alt)
            pt = self._project_angles(sam.az, sam.el, eff_fov)
            if pt is not None:
                sx, sy = pt
                flare_r = max(1, min(5, int(round((6.5 * self.zoom_x) / max(1.2, r_s * 0.6)))))
                for dy in range(-flare_r, flare_r + 1):
                    for dx in range(-flare_r, flare_r + 1):
                        if dx * dx + dy * dy <= flare_r * flare_r:
                            yy = sy + dy
                            xx = sx + dx
                            if 0 <= yy < SENSOR_H and 0 <= xx < SENSOR_W:
                                mat[yy, xx] = max(mat[yy, xx], 0.96)

        for tr in self.active_tracers:
            if not tr.active:
                continue
            prog = min(1.0, tr.elapsed / tr.travel_time_total)
            cur_az = tr.start_az + ang_diff_deg(tr.aim_az, tr.start_az) * prog
            cur_el = tr.start_el + (tr.aim_el - tr.start_el) * prog
            pt = self._project_angles(cur_az, cur_el, eff_fov)
            if pt is not None:
                tx, ty = pt
                fade_heat = max(0.46, 0.95 * (1.0 - 0.42 * prog))
                sz_t = 2 if prog < 0.35 else 1
                for dy in range(sz_t):
                    for dx in range(sz_t):
                        yy = ty + dy
                        xx = tx + dx
                        if 0 <= yy < SENSOR_H and 0 <= xx < SENSOR_W:
                            mat[yy, xx] = max(mat[yy, xx], fade_heat)

        in_fov = False
        locked = False
        px_x = SENSOR_W // 2
        px_y = SENSOR_H // 2
        size_px = 1

        if target is not None and target.alive:
            r_km, t_az, t_el = target.polar()
            d_az = ang_diff_deg(t_az, self.cam_az)
            d_el = t_el - self.cam_el

            half_fov_x = eff_fov * 0.5
            half_fov_y = (eff_fov * (SENSOR_H / SENSOR_W)) * 0.5

            if abs(d_az) <= half_fov_x and abs(d_el) <= half_fov_y:
                in_fov = True
                px_x = int(round((0.5 + d_az / eff_fov) * (SENSOR_W - 1)))
                px_y = int(round((0.5 - d_el / (eff_fov * (SENSOR_H / SENSOR_W))) * (SENSOR_H - 1)))

                if target.is_munitions:
                    proximity = max(0.0, min(1.0, (14.0 - r_km) / 14.0))
                    rapid_swell = (proximity ** 3.4) * 26.0 * (0.7 + 0.3 * self.zoom_x)
                    size_px = max(1, min(32, int(round(1.0 + rapid_swell))))
                    heat = min(0.98, 0.72 + 0.26 * (proximity ** 1.5))
                    rad_m = max(0, size_px // 2)
                    for dy in range(-rad_m, rad_m + 1):
                        for dx in range(-rad_m, rad_m + 1):
                            if rad_m == 0 or (dx * dx + dy * dy <= rad_m * rad_m + 1):
                                yy = px_y + dy
                                xx = px_x + dx
                                if 0 <= yy < SENSOR_H and 0 <= xx < SENSOR_W:
                                    mat[yy, xx] = max(mat[yy, xx], heat)
                else:
                    is_liner = (target.kind == "liner")
                    size_factor = 1.0 if is_liner else max(0.45, min(1.85, (target.rcs / 3.0) ** 0.55))
                    base_span = 55.0 if is_liner else ((10.5 if target.kind != "uav" else 4.5) * size_factor)
                    scale_zoom = float(self.zoom_x)
                    raw_size = (base_span * scale_zoom) / max(2.2, r_km * 0.42)
                    max_cap = 30 if is_liner else (15 if target.kind != "uav" else 6)
                    size_px = max(1, min(max_cap, int(round(raw_size))))

                    base_heat = 0.76 if is_liner else (0.68 if target.kind != "uav" else 0.54)
                    heat = max(0.42, min(0.76, base_heat * (0.90 + 0.12 * size_factor)))

                    if size_px <= 2:
                        for dy in range(size_px):
                            for dx in range(size_px):
                                yy = min(SENSOR_H - 1, max(0, px_y + dy))
                                xx = min(SENSOR_W - 1, max(0, px_x + dx))
                                mat[yy, xx] = max(mat[yy, xx], heat)
                    else:
                        half_w = max(1, size_px // 2)
                        wing_y = min(SENSOR_H - 1, max(0, px_y))
                        for dx in range(-half_w, half_w + 1):
                            xx = px_x + dx
                            if 0 <= xx < SENSOR_W:
                                mat[wing_y, xx] = max(mat[wing_y, xx], heat)
                        if size_px >= 6:
                            tip_y = min(SENSOR_H - 1, max(0, px_y + 1))
                            for dx in (-half_w, half_w):
                                xx = px_x + dx
                                if 0 <= xx < SENSOR_W:
                                    mat[tip_y, xx] = max(mat[tip_y, xx], heat * 0.88)
                        half_fuse = max(2, int(half_w * 0.9)) if is_liner else max(1, half_w // 2)
                        for dy in range(-half_fuse, half_fuse + 1):
                            yy = px_y + dy
                            if 0 <= yy < SENSOR_H and 0 <= px_x < SENSOR_W:
                                mat[yy, px_x] = max(mat[yy, px_x], min(0.78, heat * 1.04))

                locked = bool(target.detected and not glitch_active and not getattr(self, "notch_masked", False))

        if self.polarity == "BHOT":
            mat = 1.0 - mat

        vals = (mat * 255.0).astype(np.uint8)
        rgb = np.zeros((SENSOR_H, SENSOR_W, 3), dtype=np.uint8)
        if self.polarity == "GREEN":
            rgb[:, :, 0] = (vals * 0.15).astype(np.uint8)
            rgb[:, :, 1] = vals
            rgb[:, :, 2] = (vals * 0.22).astype(np.uint8)
        else:
            rgb[:, :, 0] = vals
            rgb[:, :, 1] = vals
            rgb[:, :, 2] = vals

        self._rgb_buf = np.ascontiguousarray(rgb).tobytes()
        qimg = QImage(self._rgb_buf, SENSOR_W, SENSOR_H, SENSOR_W * 3, QImage.Format.Format_RGB888).copy()
        self.frame_pixmap = QPixmap.fromImage(qimg)
        self._last_in_fov = in_fov
        self._last_locked = locked
        self._last_px = (px_x, px_y)
        self._last_size_px = size_px
        self.update()

    def paintEvent(self, _event):
        painter = QPainter(self)
        if not painter.isActive():
            return
        try:
            w = self.width()
            h = self.height()

            if not getattr(self, "powered", True):
                painter.fillRect(0, 0, w, h, QColor("#000000"))
                painter.setPen(QPen(QColor("#90a4ae"), 1))
                painter.setFont(QFont("Consolas", 10, QFont.Weight.Bold))
                painter.drawText(12, 22, "ОЭС / ТПВ: ПИТАНИЕ ОТКЛЮЧЕНО")
                painter.drawText(
                    QRectF(0, 0, w, h),
                    Qt.AlignmentFlag.AlignCenter,
                    "ТЕПЛОВИЗОР ВЫКЛЮЧЕН\nВКЛЮЧИТЕ СУО ДЛЯ ЗАПУСКА КАНАЛА"
                )
                return

            scaled = self.frame_pixmap.scaled(
                w, h, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.FastTransformation
            )
            painter.drawPixmap(0, 0, scaled)

            if self.zoom_glitch_sec > 0.0:
                painter.setPen(QPen(QColor("#e0f7fa"), 2))
                for _ in range(4):
                    gy = int(np.random.uniform(10, max(20, h - 10)))
                    gx0 = int(np.random.uniform(0, w * 0.35))
                    gx1 = int(np.random.uniform(w * 0.65, w))
                    painter.drawLine(gx0, gy, gx1, gy)

            hud_color = QColor("#e8f5e9") if self.polarity != "BHOT" else QColor("#1b2620")
            accent_color = QColor("#69f0ae") if self.polarity != "BHOT" else QColor("#0d47a1")
            lost_color = QColor("#ff5252")

            painter.setPen(QPen(hud_color, 1))
            painter.setFont(QFont("Consolas", 9, QFont.Weight.Bold))

            if self.target is not None and self.target.alive and self._last_in_fov:
                px_x, px_y = self._last_px
                sz_px = max(1, self._last_size_px)
                cell_w = w / SENSOR_W
                cell_h = h / SENSOR_H
                tx_c = int(round((px_x + 0.5) * cell_w))
                ty_c = int(round((px_y + 0.5) * cell_h))

                draw_col = QColor("#ff5252") if self.target.is_munitions else (accent_color if self._last_locked else hud_color)
                painter.setPen(QPen(draw_col, 1))
                painter.drawLine(tx_c - 22, ty_c, tx_c - 6, ty_c)
                painter.drawLine(tx_c + 6, ty_c, tx_c + 22, ty_c)
                painter.drawLine(tx_c, ty_c - 18, tx_c, ty_c - 5)
                painter.drawLine(tx_c, ty_c + 5, tx_c, ty_c + 18)

                if self._last_locked:
                    box = max(16, int(round(sz_px * max(cell_w, cell_h) * 0.65)) + 10)
                    painter.setPen(QPen(draw_col, 2))
                    for dx, dy in [(-1, -1), (1, -1), (-1, 1), (1, 1)]:
                        x0 = tx_c + dx * box
                        y0 = ty_c + dy * box
                        painter.drawLine(x0, y0, x0 - dx * 8, y0)
                        painter.drawLine(x0, y0, x0, y0 - dy * 8)
            else:
                cx, cy = w // 2, h // 2
                painter.drawLine(cx - 26, cy, cx - 8, cy)
                painter.drawLine(cx + 8, cy, cx + 26, cy)
                painter.drawLine(cx, cy - 20, cx, cy - 6)
                painter.drawLine(cx, cy + 6, cx, cy + 20)

            scale_x = w - 34
            painter.drawLine(scale_x, 28, scale_x, h - 28)
            for step in range(0, 7):
                yy = int(28 + step * ((h - 56) / 6.0))
                painter.drawLine(scale_x - 6, yy, scale_x + 4, yy)
                el_val = int(60 - step * 10)
                painter.drawText(scale_x + 6, yy + 4, f"{el_val}")

            glitch_tag = "  [СБОЙ ЗУМА]" if self.zoom_glitch_sec > 0.0 else ""
            painter.drawText(10, 18, f"ОЭС / ТПВ [{self.polarity}]  x{self.zoom_x}  {SENSOR_W}x{SENSOR_H}{glitch_tag}")
            painter.drawText(10, 34, f"АЗМ: {self.cam_az:05.1f}°  УМ: {self.cam_el:04.1f}°")

            if self.target is not None:
                if not self.target.alive:
                    painter.setPen(QPen(QColor("#ffd54f"), 1))
                    painter.drawText(10, h - 22, f"ЦЕЛЬ {self.target.name} ПОРАЖЕНА — УГАСАНИЕ ТЕПЛОВОГО СЛЕДА")
                else:
                    r_km, _, _ = self.target.polar()
                    sz = self._last_size_px
                    out_radar_tag = " [ЗА ПРЕДЕЛАМИ РАДАРА >36КМ]" if r_km > MAX_RANGE_KM else ""
                    if not self._last_locked:
                        state_txt = "ЗАХВАТ СБИТ (ЦЕЛЬ ПОТЕРЯНА)"
                        painter.setPen(QPen(lost_color, 1))
                    else:
                        state_txt = "УГРОЗА В ЗАХВАТЕ (ПЕРЕХВАТ)" if self.target.is_munitions else (
                            "ЗАХВАТ / АВТОСОПРОВОЖДЕНИЕ" if self.auto_track else "ЗАХВАТ / РУЧНОЕ"
                        )
                        painter.setPen(QPen(QColor("#ff5252") if self.target.is_munitions else accent_color, 1))
                    painter.drawText(10, h - 22, f"ЦЕЛЬ: {self.target.name} | Д={r_km:.1f} км{out_radar_tag} | ПЯТНО: {sz}x{sz}п")
                    painter.drawText(10, h - 8, f"СТАТУС: {state_txt}")
        finally:
            painter.end()


class OesSectorSideWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.setMinimumSize(210, 180)
        self.cam_az = 35.0
        self.cam_el = 15.0
        self.target = None

    def update_sector(self, cam_az, cam_el, target):
        self.cam_az = cam_az
        self.cam_el = cam_el
        self.target = target
        self.update()

    def paintEvent(self, _event):
        painter = QPainter(self)
        if not painter.isActive():
            return
        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            w = self.width()
            h = self.height()

            painter.fillRect(0, 0, w, h, QColor("#8d9164"))
            painter.setPen(QPen(QColor("#3e4228"), 2))
            painter.drawRect(1, 1, w - 2, h - 2)

            trap_top_y = 12
            trap_bot_y = int(h * 0.34)
            cx = w // 2
            trap = QPolygonF([
                QPointF(cx - 32, trap_top_y),
                QPointF(cx + 32, trap_top_y),
                QPointF(cx + 52, trap_bot_y),
                QPointF(cx - 52, trap_bot_y),
            ])
            painter.setBrush(QBrush(QColor("#ce93d8")))
            painter.setPen(QPen(QColor("#263238"), 1))
            painter.drawPolygon(trap)

            el_ratio = max(0.0, min(1.0, self.cam_el / 60.0))
            active_y = trap_bot_y - int(el_ratio * (trap_bot_y - trap_top_y - 8))
            active_trap = QPolygonF([
                QPointF(cx - 34, max(trap_top_y + 2, active_y - 6)),
                QPointF(cx + 34, max(trap_top_y + 2, active_y - 6)),
                QPointF(cx + 46, min(trap_bot_y - 2, active_y + 6)),
                QPointF(cx - 46, min(trap_bot_y - 2, active_y + 6)),
            ])
            painter.setBrush(QBrush(QColor("#ffee58")))
            painter.drawPolygon(active_trap)

            sec_cy = int(h * 0.88)
            sec_r = min(int(w * 0.44), int(h * 0.48))
            if sec_r > 20:
                rect = QRectF(cx - sec_r, sec_cy - sec_r, sec_r * 2, sec_r * 2)
                painter.setBrush(QBrush(QColor("#ce93d8")))
                painter.drawPie(rect, 35 * 16, 110 * 16)

                span = 36
                painter.setBrush(QBrush(QColor("#ffee58")))
                painter.drawPie(rect, int((90.0 - span * 0.5) * 16), int(span * 16))

                painter.setPen(QPen(QColor("#1b5e20"), 2))
                painter.drawLine(QPointF(cx, sec_cy), QPointF(cx, sec_cy - sec_r))

                if self.target is not None and self.target.alive and self.target.detected and not self.target.clutter_notched:
                    r_slant, t_az, _ = self.target.polar()
                    d_az = ang_diff_deg(t_az, self.cam_az)
                    if abs(d_az) <= 55.0:
                        rad = math.radians(d_az)
                        r_dist = min(1.0, r_slant / MAX_RANGE_KM) * (sec_r - 6)
                        tx = cx + r_dist * math.sin(rad)
                        ty = sec_cy - r_dist * math.cos(rad)
                        painter.setBrush(QBrush(QColor("#ff5252") if self.target.is_munitions else QColor("#00e676")))
                        painter.setPen(QPen(QColor("#000000"), 1))
                        painter.drawEllipse(QPointF(tx, ty), 4.0, 4.0)

            painter.setPen(QColor("#11161b"))
            painter.setFont(QFont("Consolas", 8, QFont.Weight.Bold))
            painter.drawText(8, 14, "СЕКТОР ОЭС")
            painter.drawText(8, h - 8, f"АЗМ {self.cam_az:05.1f}°  УМ {self.cam_el:02.0f}°")
        finally:
            painter.end()


class TacticalRadarWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.setMinimumSize(460, 420)
        self.beam_az = 0.0
        self.dashed_az = 180.0
        self.sector_center = 0.0
        self.sector_width = 90.0
        self.sector_mode = False
        self.arc180_mode = False
        self.no_lock_scan = False
        self.arc180_width = 180.0
        self.targets = []
        self.selected_idx = 0
        self.active_sams = []
        self.channel_assignments = {}

    def update_radar(
        self, beam_az, targets, selected_idx, sector_mode, sector_center, sector_width,
        arc180_mode=False, dashed_az=None, no_lock_scan=False, active_sams=None, channel_assignments=None
    ):
        self.beam_az = beam_az
        self.dashed_az = ((beam_az + 180.0) % 360.0) if dashed_az is None else dashed_az
        self.targets = targets
        self.selected_idx = selected_idx
        self.sector_mode = sector_mode
        self.sector_center = sector_center
        self.sector_width = sector_width
        self.arc180_mode = arc180_mode
        self.no_lock_scan = bool(no_lock_scan)
        self.active_sams = active_sams or []
        self.channel_assignments = channel_assignments or {}
        self.update()

    def paintEvent(self, _event):
        painter = QPainter(self)
        if not painter.isActive():
            return
        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            w = self.width()
            h = self.height()

            painter.fillRect(0, 0, w, h, QColor("#091526"))

            cx = w // 2
            cy = h // 2 + 8
            radius = min(w, h) // 2 - 34
            if radius < 40:
                return

            for i in range(1, 5):
                r_px = int(radius * (i / 4.0))
                pen_col = QColor("#2a4d7a")
                painter.setPen(QPen(pen_col, 1, Qt.PenStyle.DashLine if i != 4 else Qt.PenStyle.SolidLine))
                painter.drawEllipse(QPointF(cx, cy), r_px, r_px)
                painter.setPen(QColor("#78a6d8"))
                painter.setFont(QFont("Consolas", 8))
                km_label = int(MAX_RANGE_KM * (i / 4.0))
                painter.drawText(cx + 4, cy - r_px + 11, f"{km_label}")

            painter.setPen(QPen(QColor("#1e3b60"), 1))
            for deg in range(0, 360, 30):
                rad = math.radians(deg)
                ex = cx + radius * math.sin(rad)
                ey = cy - radius * math.cos(rad)
                painter.drawLine(QPointF(cx, cy), QPointF(ex, ey))

            arc_r = int(radius * 0.78)
            half_180 = self.arc180_width * 0.5
            r_left = math.radians(self.sector_center - half_180)
            r_right = math.radians(self.sector_center + half_180)
            red_pen = QPen(QColor("#e91e63") if self.arc180_mode else QColor("#ad1457"), 2)
            painter.setPen(red_pen)
            painter.drawLine(QPointF(cx, cy), QPointF(cx + arc_r * math.sin(r_left), cy - arc_r * math.cos(r_left)))
            painter.drawLine(QPointF(cx, cy), QPointF(cx + arc_r * math.sin(r_right), cy - arc_r * math.cos(r_right)))
            arc_rect = QRectF(cx - arc_r, cy - arc_r, arc_r * 2, arc_r * 2)
            start_qt_180 = int((90.0 - (self.sector_center + half_180)) * 16)
            span_qt_180 = int(self.arc180_width * 16)
            painter.drawArc(arc_rect, start_qt_180, span_qt_180)

            half_w = self.sector_width * 0.5
            s_left = math.radians(self.sector_center - half_w)
            s_right = math.radians(self.sector_center + half_w)
            painter.setPen(QPen(QColor("#ffd54f"), 2))
            painter.drawLine(QPointF(cx, cy), QPointF(cx + radius * math.sin(s_left), cy - radius * math.cos(s_left)))
            painter.drawLine(QPointF(cx, cy), QPointF(cx + radius * math.sin(s_right), cy - radius * math.cos(s_right)))

            rect = QRectF(cx - radius, cy - radius, radius * 2, radius * 2)
            start_qt_sec = int((90.0 - (self.sector_center + half_w)) * 16)
            span_qt_sec = int(self.sector_width * 16)
            painter.drawArc(rect, start_qt_sec, span_qt_sec)

            b_rad = math.radians(self.beam_az)
            eff_dashed_az = self.beam_az if self.no_lock_scan else self.dashed_az
            d_rad = math.radians(eff_dashed_az)
            if not self.no_lock_scan:
                painter.setPen(QPen(QColor("#4dd0e1"), 1.5, Qt.PenStyle.DashLine))
                painter.drawLine(QPointF(cx, cy), QPointF(cx + radius * math.sin(d_rad), cy - radius * math.cos(d_rad)))
            painter.setPen(QPen(QColor("#69f0ae"), 2))
            painter.drawLine(QPointF(cx, cy), QPointF(cx + radius * math.sin(b_rad), cy - radius * math.cos(b_rad)))

            for sam in self.active_sams:
                if not sam.active:
                    continue
                r_s = math.hypot(math.hypot(sam.x, sam.y), sam.alt)
                if r_s > MAX_RANGE_KM:
                    continue
                r_n = min(1.0, r_s / MAX_RANGE_KM)
                rad_s = math.radians(sam.az)
                sx = cx + (radius * r_n) * math.sin(rad_s)
                sy = cy - (radius * r_n) * math.cos(rad_s)
                painter.setPen(QPen(QColor("#ffab40"), 2))
                painter.setBrush(QBrush(QColor("#ffab40")))
                painter.drawEllipse(QPointF(sx, sy), 3.0, 3.0)

            painter.setFont(QFont("Consolas", 8, QFont.Weight.Bold))
            active_count = 0
            out_of_radar_count = 0
            for idx, t in enumerate(self.targets):
                if not t.alive:
                    continue
                r_raw, raw_az, _ = t.polar()
                if r_raw > MAX_RANGE_KM:
                    out_of_radar_count += 1
                    continue
                if self.sector_mode and abs(ang_diff_deg(raw_az, self.sector_center)) > half_w:
                    continue
                if self.arc180_mode and abs(ang_diff_deg(raw_az, self.sector_center)) > half_180:
                    continue
                is_locked_target = (not self.no_lock_scan) and (idx == self.selected_idx)
                live_ok = bool(t.detected and not t.clutter_notched)

                if live_ok:
                    active_count += 1
                    if is_locked_target or t.is_munitions:
                        r_slant, az, _ = t.polar()
                        hdg_deg = t.heading_deg()
                        spd_val = t.speed()
                        alt_val = t.alt
                        is_inter_sweep = False
                    else:
                        r_slant, az, _ = t.swept_polar()
                        hdg_deg = t.swept_heading_deg()
                        spd_val = t.radar_speed
                        alt_val = t.radar_alt
                        is_inter_sweep = (t.radar_update_flash <= 0.05)
                    alpha = 1.0
                    coasting = False
                elif t.track_visible and t.blip_alpha > 0.01:
                    r_slant, az, _ = t.display_polar()
                    hdg_deg = t.heading_deg()
                    spd_val = t.speed()
                    alt_val = t.alt
                    alpha = t.blip_alpha
                    coasting = True
                    is_inter_sweep = False
                else:
                    continue

                if r_slant > MAX_RANGE_KM:
                    continue

                r_norm = min(1.0, r_slant / MAX_RANGE_KM)
                rad = math.radians(az)
                tx = cx + (radius * r_norm) * math.sin(rad)
                ty = cy - (radius * r_norm) * math.cos(rad)

                if t.is_munitions:
                    base_col = QColor("#ff1744")
                elif coasting:
                    base_col = QColor("#ff9800")
                elif is_locked_target:
                    base_col = QColor("#ffee58")
                elif t.radar_update_flash > 0.25:
                    base_col = QColor("#69f0ae")
                else:
                    base_col = QColor("#90caf9")

                col = QColor(base_col)
                col.setAlphaF(max(0.0, min(1.0, alpha)))

                hdg_rad = math.radians(hdg_deg)
                vx_end = tx + 14 * math.sin(hdg_rad)
                vy_end = ty - 14 * math.cos(hdg_rad)
                painter.setPen(QPen(col, 2, Qt.PenStyle.DashLine if (coasting or is_inter_sweep) else Qt.PenStyle.SolidLine))
                painter.drawLine(QPointF(tx, ty), QPointF(vx_end, vy_end))

                ch_badge = f" [{self.channel_assignments[t.id]['mode']}]" if t.id in self.channel_assignments else ""

                if coasting:
                    painter.setPen(QPen(col, 2))
                    painter.setBrush(QBrush(Qt.BrushStyle.NoBrush))
                    painter.drawEllipse(QPointF(tx, ty), 5.0, 5.0)
                    rem_coast = max(0.0, COAST_DURATION_SEC - t.coast_elapsed)
                    tag = f" [ПРОГНОЗ {rem_coast:.1f}с]" if t.coast_elapsed < COAST_DURATION_SEC else " [УГАСАНИЕ]"
                else:
                    painter.setPen(QPen(col, 2))
                    painter.setBrush(QBrush(col) if not is_inter_sweep else QBrush(Qt.BrushStyle.NoBrush))
                    dot_r = 6.5 if t.kind == "liner" else (4.5 if is_locked_target else 3.8)
                    painter.drawEllipse(QPointF(tx, ty), dot_r, dot_r)
                    if is_locked_target or t.is_munitions:
                        painter.drawRect(QRectF(tx - 8, ty - 8, 16, 16))
                    tag = " [УГРОЗА!]" if t.is_munitions else (
                        "" if is_locked_target else (" [ОБНОВЛ.]" if t.radar_update_flash > 0.25 else " [ПРОГН. ТРЕК]")
                    )

                painter.setPen(col)
                painter.drawText(int(tx + 9), int(ty - 3), f"Ц{t.id} {r_slant:.1f}км{ch_badge}{tag}")
                painter.drawText(int(tx + 9), int(ty + 8), f"V={int(spd_val)} H={alt_val:.1f}")

            painter.setPen(QColor("#b3e5fc"))
            painter.setFont(QFont("Consolas", 9, QFont.Weight.Bold))
            mode_str = f"СЕКТОР {int(self.sector_width)}°" if self.sector_mode else "КРУГОВОЙ 360°"
            zone180_str = " | ЗОНА 180°: АКТИВ" if self.arc180_mode else ""
            lock_mode_str = " | СКАН БЕЗ ЗАХВАТА" if self.no_lock_scan else ""
            out_str = f" | ЗА РАДАРОМ (>36КМ): {out_of_radar_count}" if out_of_radar_count > 0 else ""
            painter.drawText(10, 18, f"РЕЖИМ РЛС: {mode_str}{zone180_str}{lock_mode_str}{out_str} | ЛУЧ: {self.beam_az:05.1f}°")
            painter.drawText(w - 175, 18, f"ЦЕЛЕЙ НА СОПР.: {active_count}")
        finally:
            painter.end()


class DestroyedOverlayWidget(QWidget):
    def __init__(self, on_return_callback, parent=None):
        super().__init__(parent)
        self.on_return_callback = on_return_callback
        self.munitions_name = "НЕИЗВЕСТНЫЙ БОЕПРИПАС"
        self.hide()

        layout = QVBoxLayout(self)
        layout.setContentsMargins(24, 24, 24, 34)
        layout.addStretch(1)

        self.lbl_killer = QLabel("")
        self.lbl_killer.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.lbl_killer.setWordWrap(True)
        self.lbl_killer.setStyleSheet(
            "color: #ff1744; background-color: rgba(0, 0, 0, 195); "
            "border: 2px solid #ff1744; padding: 12px 18px; "
            "font-family: Consolas, monospace; font-size: 20px; font-weight: bold;"
        )
        layout.addWidget(self.lbl_killer)

        btn_row = QHBoxLayout()
        btn_row.addStretch(1)
        self.btn_return = QPushButton("Вернуться к началу")
        self.btn_return.setMinimumSize(240, 44)
        self.btn_return.setStyleSheet(
            "QPushButton { background-color: #d50000; color: #ffffff; border: 2px solid #ff8a80; "
            "font-family: Consolas, monospace; font-size: 15px; font-weight: bold; padding: 8px 20px; }"
            "QPushButton:hover { background-color: #ff1744; }"
        )
        self.btn_return.clicked.connect(self._handle_return)
        btn_row.addWidget(self.btn_return)
        btn_row.addStretch(1)
        layout.addLayout(btn_row)

    def show_destroyed(self, munitions_name):
        self.munitions_name = munitions_name
        self.lbl_killer.setText(f"КОМПЛЕКС «ПАНЦИРЬ-С1» ПОРАЖЁН БОЕПРИПАСОМ: {munitions_name}")
        if self.parent() is not None:
            self.setGeometry(self.parent().rect())
        self.show()
        self.raise_()
        self.update()

    def _handle_return(self):
        self.hide()
        if callable(self.on_return_callback):
            self.on_return_callback()

    def paintEvent(self, _event):
        p = QPainter(self)
        if not p.isActive():
            return
        w = self.width()
        h = self.height()
        p.fillRect(0, 0, w, h, QColor(12, 12, 14, 235))

        for _ in range(180):
            ny = random.randint(0, max(1, h - 4))
            nx = random.randint(0, max(1, w - 40))
            nw = random.randint(25, max(40, w // 2))
            nh = random.randint(1, 5)
            shade = random.randint(45, 240)
            p.fillRect(nx, ny, nw, nh, QColor(shade, shade, shade, random.randint(90, 210)))

        for _ in range(14):
            gy = random.randint(0, max(1, h - 2))
            col = QColor(255, 23, 68, 170) if random.random() < 0.35 else QColor(224, 247, 250, 160)
            p.setPen(QPen(col, random.randint(1, 3)))
            p.drawLine(0, gy, w, gy)

        p.setPen(QColor("#ff5252"))
        p.setFont(QFont("Consolas", 22, QFont.Weight.Bold))
        p.drawText(QRectF(0, h * 0.25, w, 60), Qt.AlignmentFlag.AlignCenter, "ПОТЕРЯ СИГНАЛА СУО / КРИТИЧЕСКОЕ ПОРАЖЕНИЕ")
        p.end()


def detection_threshold(noise_level):
    return 0.18 + (noise_level ** 1.15) * 3.1 + (0.35 if noise_level >= 0.70 else 0.0)


def ascope_curve(noise_level, targets, n=420, rng=None):
    rng = rng or np.random.default_rng()
    thr = detection_threshold(noise_level)
    sigma = thr / 4.2
    x = np.linspace(0.0, MAX_RANGE_KM, n)
    sig = 0.5 * thr * np.exp(-x / 2.5)
    for r_km, amp in targets:
        sig = sig + amp * np.exp(-0.5 * ((x - r_km) / 0.45) ** 2)
    n1 = rng.normal(0.0, sigma, n)
    n2 = rng.normal(0.0, sigma, n)
    y = np.sqrt((sig + n1) ** 2 + n2 ** 2)
    ymax = max(thr * 1.8, min(float(sig.max()) * 1.1, thr * 6.0))
    return x, y, thr, ymax


def doppler_curve(noise_level, f0_ghz, fd_khz, amp, n=700, rng=None):
    rng = rng or np.random.default_rng()
    thr = detection_threshold(noise_level)
    sigma = thr / 4.2
    f0 = f0_ghz * 1e9
    fmax = 2.0 * 350.0 * f0 / C / 1000.0
    notch = 2.0 * NOTCH_VR_MS * f0 / C / 1000.0
    x = np.linspace(-fmax, fmax, n)
    clutter = 2.2 * thr
    sig = clutter * np.exp(-0.5 * (x / max(0.10, notch * 0.25)) ** 2)
    top = clutter
    if fd_khz is not None and amp is not None:
        w = max(0.15, notch * 0.35)
        sig = sig + amp * np.exp(-0.5 * ((x - fd_khz) / w) ** 2)
        top = max(top, amp)
    n1 = rng.normal(0.0, sigma, n)
    n2 = rng.normal(0.0, sigma, n)
    y = np.sqrt((sig + n1) ** 2 + n2 ** 2)
    ymax = max(thr * 1.8, min(top * 1.1, thr * 5.0))
    return x, y, thr, ymax, notch


class JammingPlotWidget(QWidget):
    BG = QColor("#07140d")
    GRID = QColor(46, 110, 70, 120)
    TXT = QColor("#7fe6a6")

    def __init__(self, mode):
        super().__init__()
        self.mode = mode
        self.setMinimumSize(420, 200)
        self.noise_level = 0.2
        self.f0_ghz = 3.0
        self.items = []
        self.sel = None
        self.note = ""
        self.powered = True
        self.rng = np.random.default_rng()

    def set_powered(self, powered):
        powered = bool(powered)
        if powered != self.powered:
            self.powered = powered
            self.update()

    def set_data(self, noise_level, f0_ghz, items, sel, note=""):
        self.note = note
        self.noise_level = noise_level
        self.f0_ghz = f0_ghz
        self.items = items
        self.sel = sel
        self.update()

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.fillRect(self.rect(), self.BG)
        font = QFont("Consolas", 9)
        p.setFont(font)

        if not self.powered:
            title = "А-РАЗВЁРТКА" if self.mode == "ascope" else "ДОПЛЕРОВСКИЙ СПЕКТР"
            p.fillRect(self.rect(), QColor("#050a07"))
            p.setPen(QColor(84, 110, 122))
            p.drawText(QRectF(0, 6, self.width(), 18), Qt.AlignmentFlag.AlignCenter, title)
            p.setPen(QColor(255, 82, 82))
            p.setFont(QFont("Consolas", 12, QFont.Weight.Bold))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "СУО ОТКЛЮЧЕНА\nНЕТ СИГНАЛА")
            p.end()
            return

        ml, mr, mt, mb = 56, 16, 30, 38
        rect = QRectF(ml, mt, max(10, self.width() - ml - mr), max(10, self.height() - mt - mb))

        if self.mode == "ascope":
            x, y, thr, ymax = ascope_curve(
                self.noise_level, [(it[1], it[2]) for it in self.items], rng=self.rng
            )
            x0, x1 = 0.0, MAX_RANGE_KM
            title = "А-РАЗВЁРТКА: эхо-сигнал (амплитуда от дальности)"
            xlabel = "Дальность, км (t = 2R/c)"
            xticks = [i * 6.0 for i in range(7)]
            notch = None
        else:
            fd = self.sel[0] if self.sel else None
            amp = self.sel[1] if self.sel else None
            x, y, thr, ymax, notch = doppler_curve(
                self.noise_level, self.f0_ghz, fd, amp, rng=self.rng
            )
            x0, x1 = float(x[0]), float(x[-1])
            title = "ДОПЛЕРОВСКИЙ СПЕКТР выбранной цели (БПФ)"
            xlabel = "Доплеровский сдвиг fd, кГц"
            step = 2.0 if x1 > 5.0 else 1.0
            xticks = [k * step for k in range(int(-x1 // step), int(x1 // step) + 1)]

        def px(v):
            return rect.left() + (v - x0) / (x1 - x0) * rect.width()

        def py(v):
            return rect.bottom() - (v / ymax) * rect.height()

        p.setPen(QPen(self.GRID, 1, Qt.PenStyle.DotLine))
        for xt in xticks:
            if x0 <= xt <= x1:
                p.drawLine(QPointF(px(xt), rect.top()), QPointF(px(xt), rect.bottom()))
        for k in range(5):
            gy = rect.bottom() - rect.height() * k / 4.0
            p.drawLine(QPointF(rect.left(), gy), QPointF(rect.right(), gy))
        p.setPen(self.TXT)
        for xt in xticks:
            if x0 <= xt <= x1:
                p.drawText(QRectF(px(xt) - 24, rect.bottom() + 3, 48, 14),
                           Qt.AlignmentFlag.AlignCenter, f"{xt:g}")
        for k in range(5):
            val = ymax * k / 4.0
            gy = rect.bottom() - rect.height() * k / 4.0
            p.drawText(QRectF(2, gy - 8, ml - 8, 16),
                       Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, f"{val:.1f}")
        p.drawText(QRectF(rect.left(), rect.bottom() + 18, rect.width(), 16),
                   Qt.AlignmentFlag.AlignCenter, xlabel)
        p.drawText(QRectF(rect.left(), 6, rect.width(), 18), Qt.AlignmentFlag.AlignCenter, title)

        p.setPen(QPen(QColor(46, 110, 70), 1))
        p.drawRect(rect)

        p.save()
        p.setClipRect(rect)

        if notch is not None:
            p.fillRect(QRectF(px(-notch), rect.top(), px(notch) - px(-notch), rect.height()),
                       QColor(255, 82, 82, 45))
            p.setPen(QPen(QColor(255, 82, 82, 160), 1, Qt.PenStyle.DashLine))
            p.drawLine(QPointF(px(-notch), rect.top()), QPointF(px(-notch), rect.bottom()))
            p.drawLine(QPointF(px(notch), rect.top()), QPointF(px(notch), rect.bottom()))
            p.setPen(QPen(QColor(120, 200, 150, 140), 1, Qt.PenStyle.DashLine))
            p.drawLine(QPointF(px(0.0), rect.top()), QPointF(px(0.0), rect.bottom()))

        poly = QPolygonF([QPointF(px(float(a)), py(float(b))) for a, b in zip(x, y)])
        curve_color = QColor("#00e676") if self.mode == "ascope" else QColor("#ffca28")
        p.setPen(QPen(curve_color, 1.4))
        p.drawPolyline(poly)

        p.setPen(QPen(QColor(255, 138, 101), 1.3, Qt.PenStyle.DashLine))
        p.drawLine(QPointF(rect.left(), py(thr)), QPointF(rect.right(), py(thr)))
        p.restore()

        p.setPen(QColor(255, 138, 101))
        p.drawText(QRectF(rect.right() - 170, max(rect.top(), py(thr) - 16), 166, 14),
                   Qt.AlignmentFlag.AlignRight, f"ПОРОГ {thr:.2f}")

        if self.mode == "ascope":
            for tid, r_km, amp, det, is_sel, notched in self.items:
                if r_km > MAX_RANGE_KM:
                    continue
                ty = max(rect.top() + 12, py(amp) - 4)
                col = QColor("#ffeb3b") if is_sel else (QColor("#00e676") if det else QColor("#ef9a9a"))
                if notched:
                    col = QColor("#ff5252")
                p.setPen(col)
                p.drawText(QPointF(px(r_km) + 3, ty), f"Ц{tid} РЕЖ." if notched else f"Ц{tid}")
        else:
            p.setPen(QColor(255, 82, 82))
            p.drawText(QRectF(px(-notch), rect.top() + 2, px(notch) - px(-notch), 14),
                       Qt.AlignmentFlag.AlignCenter, "РЕЖЕКЦИЯ")
            if self.note:
                p.setPen(QColor(255, 82, 82))
                p.drawText(QRectF(rect.left() + 6, rect.top() + 18, rect.width() - 12, 14),
                           Qt.AlignmentFlag.AlignLeft, self.note)
            elif self.sel is not None:
                fd, _amp, vr, det = self.sel
                p.setPen(QColor("#ffeb3b"))
                lbl = f"fd={fd:+.2f} кГц"
                if abs(vr) < NOTCH_VR_MS:
                    lbl += "  (в полосе режекции)"
                p.drawText(QRectF(rect.left() + 6, rect.top() + 18, rect.width() - 12, 14),
                           Qt.AlignmentFlag.AlignLeft, lbl)
        p.end()


class PantsirCombatWorkstation(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("АРМ оператора ОЭС/РЛК Панцирь-С1 — Боевой модуль")
        self.setStyleSheet("""
            QMainWindow { background-color: #c7ccd1; color: #11161b; }
            QTabWidget::pane {
                border: 2px solid #5c6670;
                background-color: #cfd4d9;
                top: -1px;
            }
            QTabBar::tab {
                background-color: #9aa3ad; color: #11161b;
                border: 2px solid #5c6670; border-bottom: none;
                padding: 8px 20px; margin-right: 4px;
                font-family: Consolas, monospace; font-size: 13px; font-weight: bold;
            }
            QTabBar::tab:selected {
                background-color: #d8dee4; color: #000000;
                border-bottom: 2px solid #d8dee4;
            }
            QFrame#BezelFrame {
                background-color: #1c2024;
                border: 4px solid #101316;
                border-radius: 5px;
            }
            QFrame#PanelBlock {
                background-color: #dce1e6;
                border: 1px solid #7d8791;
                border-radius: 3px;
            }
            QFrame#OliveBar {
                background-color: #9e9d5c;
                border: 1px solid #5c5b32;
                border-radius: 3px;
            }
            QLabel { font-family: Consolas, monospace; font-size: 11.5px; color: #11161b; }
            QPushButton {
                background-color: #e6ebf0; color: #11161b;
                border: 1px solid #5c6670; border-radius: 2px;
                padding: 4px 7px; font-family: Consolas, monospace;
                font-size: 11px; font-weight: bold;
            }
            QPushButton:hover { background-color: #ffffff; }
            QPushButton:checked {
                background-color: #76ff03; color: #0b1a0e; border: 1px solid #2e7d32;
            }
            QComboBox, QSpinBox, QListWidget {
                background-color: #ffffff; color: #11161b;
                border: 1px solid #5c6670; padding: 2px 5px;
                font-family: Consolas, monospace; font-size: 11px;
            }
            QTableWidget {
                background-color: #263238; color: #eceff1;
                gridline-color: #546e7a; font-family: Consolas, monospace; font-size: 10.5px;
            }
            QHeaderView::section {
                background-color: #455a64; color: #ffffff; font-size: 10px; padding: 2px;
            }
        """)

        self.sound_engine = SoundEngine(self)
        self.suo_powered = False
        self.combat_mode = False
        self.no_lock_scan = False
        self.is_running = True
        self.sim_time_sec = 0.0
        self.active_scenario_name = "Стандартная обстановка"
        self.event_log_lines = []
        self._prev_target_states = {}
        self.beam_az = 0.0
        self.sector_mode = False
        self.arc180_mode = False
        self.sector_follow_target = True
        self.sector_center = 35.0
        self.sector_width = 90.0
        self.sector_dir = 1
        self.f0_ghz = 3.0
        self.noise_level = 0.22
        self.cam_az = 35.0
        self.cam_el = 15.0

        # Настраиваемый состав противников для боевого режима
        self.custom_combat_roster = [
            "Су-30СМ (Ударный)",
            "F-16C (SEAD / ПРР)",
            "Rafale (Многоцелевой)",
            "БПЛА-разведчик",
        ]

        # Боевые параметры и каналы (3 РК + 1 SACLOS + 1 ОЭС = 5, из них 2 направленные)
        self.selected_weapon = "GUN"
        self.gun_trigger_held = False
        self.gun_ammo = GUN_MAX_AMMO
        self.gun_temp = TEMP_AMBIENT
        self.gun_jammed = False
        self.gun_shot_accum = 0.0
        self.gun_range_limit_enabled = True

        self.sam_ammo = SAM_MAX_AMMO
        self.sam_cooldown = 0.0
        self.next_sam_id = 1
        self.next_target_id = 10
        self.active_sams = []
        self.active_tracers = []

        self.channel_assignments = {}
        self.latest_threat_target_id = None

        self.targets = []
        self._init_targets()
        self._init_ui()

        self.destroyed_overlay = DestroyedOverlayWidget(self._return_to_initial_non_combat, parent=self)

        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(45)

        self._apply_suo_power_state(self.suo_powered)
        self._log_event("АРМ Панцирь-С1 запущен. СУО выключена — включите «СУО» для запитки ОЭС и РЛС", "WARN")
        self.showFullScreen()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self, "destroyed_overlay") and self.destroyed_overlay.isVisible():
            self.destroyed_overlay.setGeometry(self.rect())

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape and self.isFullScreen():
            self.showNormal()
        elif event.key() == Qt.Key.Key_F11:
            if self.isFullScreen():
                self.showNormal()
            else:
                self.showFullScreen()
        else:
            super().keyPressEvent(event)

    def _init_targets(self):
        self.targets = [
            SimTarget(1, "Су-30СМ (Истребитель)", "fighter", 14.0, 22.0, 6.5, -180.0, -140.0, rcs=5.0),
            SimTarget(2, "F-16C (Такт. истреб.)", "fighter", -18.0, 16.0, 4.8, 160.0, -110.0, rcs=3.2),
            SimTarget(3, "БПЛА (Разведчик)", "uav", 8.5, 11.0, 2.2, -35.0, -45.0, rcs=0.6),
            SimTarget(4, "Rafale (Многоцелевой)", "fighter", 24.0, -12.0, 7.2, -190.0, 95.0, rcs=3.5),
        ]
        self.next_target_id = 5

    def _build_combat_targets_from_roster(self, roster_list, count_desired):
        """Создаёт цели боевого режима на большой дальности (27–40 км) с возможностью залёта за радар на +4 км."""
        items = list(roster_list) if roster_list else list(ENEMY_TEMPLATES.keys())
        if count_desired <= 0:
            count_desired = len(items)
        chosen = []
        for i in range(count_desired):
            chosen.append(items[i % len(items)])

        created = []
        max_out = MAX_RANGE_KM + COMBAT_EXTRA_OUT_KM  # 40.0 км
        for idx, model_name in enumerate(chosen):
            kind, rcs, ordnance = ENEMY_TEMPLATES.get(
                model_name, ("fighter", 3.5, ["УР воздух-поверхность"])
            )
            nid = idx + 1
            # Появляются дальше (27–40 км) под разными углами
            ang = ((idx * (360.0 / max(1, len(chosen)))) + random.uniform(-18.0, 18.0)) % 360.0
            rad_az = math.radians(ang)
            spawn_dist = random.uniform(27.0, 39.0)
            x = spawn_dist * math.sin(rad_az)
            y = spawn_dist * math.cos(rad_az)
            alt = random.uniform(1.6, 8.2) if kind == "fighter" else random.uniform(1.0, 3.2)
            spd = random.uniform(155.0, 225.0) if kind == "fighter" else random.uniform(42.0, 78.0)
            # Часть целей идёт внутрь зоны, часть — по касательной/наружу с залётом до +7 км за радар
            hdg_deg = (ang + random.choice([145.0, 180.0, 215.0, 105.0, 255.0])) % 360.0
            rad_h = math.radians(hdg_deg)
            vx = spd * math.sin(rad_h)
            vy = spd * math.cos(rad_h)
            t = SimTarget(
                nid, model_name, kind, x, y, alt, vx, vy,
                rcs=rcs, ordnance_list=ordnance, is_munitions=False, max_out_km=max_out
            )
            created.append(t)
        self.next_target_id = len(created) + 1
        return created

    def _reset_combat_systems(self):
        self.gun_trigger_held = False
        self.gun_ammo = GUN_MAX_AMMO
        self.gun_temp = TEMP_AMBIENT
        self.gun_jammed = False
        self.gun_shot_accum = 0.0
        self.sam_ammo = SAM_MAX_AMMO
        self.sam_cooldown = 0.0
        self.active_sams.clear()
        self.active_tracers.clear()
        self.channel_assignments.clear()
        self.latest_threat_target_id = None
        if hasattr(self, "btn_threat_jump"):
            self.btn_threat_jump.setEnabled(False)
            self.btn_threat_jump.setText("НЕТ УГРОЗ В ВОЗДУХЕ")

    def _init_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(6, 6, 6, 6)
        root.setSpacing(4)

        top_bar = QFrame()
        top_bar.setObjectName("PanelBlock")
        top_layout = QHBoxLayout(top_bar)
        top_layout.setContentsMargins(8, 4, 8, 4)

        self.lbl_sys_ready = QLabel(" СУО ОТКЛЮЧЕНА ")
        self.lbl_sys_ready.setStyleSheet("background-color: #ff5252; color: #fff; font-weight: bold; padding: 2px 6px;")
        top_layout.addWidget(self.lbl_sys_ready)

        self.btn_suo_power = QPushButton("СУО: ВЫКЛ")
        self.btn_suo_power.setCheckable(True)
        self.btn_suo_power.setChecked(False)
        self.btn_suo_power.setStyleSheet(
            "QPushButton { background-color: #c8e6c9; color: #0b2e13; border: 1px solid #2e7d32; font-weight: bold; padding: 2px 8px; }"
            "QPushButton:checked { background-color: #76ff03; color: #000; border: 1px solid #2e7d32; }"
        )
        self.btn_suo_power.clicked.connect(self._toggle_suo_power)
        top_layout.addWidget(self.btn_suo_power)

        self.lbl_mode_badge = QLabel(" РЕЖИМ: УЧЕБНЫЙ ")
        self.lbl_mode_badge.setStyleSheet("background-color: #b0bec5; color: #000; font-weight: bold; padding: 2px 6px;")
        top_layout.addWidget(self.lbl_mode_badge)

        self.lbl_chan_info = QLabel(" КАНАЛЫ: РК 0/3 | SACLOS 0/1 | ОЭС 0/1 (НАПР: 0/2) ")
        self.lbl_chan_info.setStyleSheet("background-color: #ffd54f; color: #000; font-weight: bold; padding: 2px 6px;")
        top_layout.addWidget(self.lbl_chan_info)

        top_layout.addStretch(1)

        self.lbl_top_telem = QLabel("ВЫБРАНА ЦЕЛЬ: —")
        self.lbl_top_telem.setStyleSheet("font-weight: bold; color: #0d47a1;")
        top_layout.addWidget(self.lbl_top_telem)

        lbl_keys = QLabel(" [F11: полный экран | Esc: окно] ")
        lbl_keys.setStyleSheet("color: #455a64;")
        top_layout.addWidget(lbl_keys)

        root.addWidget(top_bar)

        self.tabs = QTabWidget()
        root.addWidget(self.tabs, stretch=1)

        self.tab_oes = QWidget()
        self.tabs.addTab(self.tab_oes, "МОНИТОР 1 (ЛЕВЫЙ): ОЭС / ТЕПЛОВИЗОР / ВООРУЖЕНИЕ")
        self._build_oes_tab(self.tab_oes)

        self.tab_radar = QWidget()
        self.tabs.addTab(self.tab_radar, "МОНИТОР 2 (ПРАВЫЙ): РАДИОЛОКАЦИОННЫЙ ОБЗОР")
        self._build_radar_tab(self.tab_radar)

        self.tab_extra = QWidget()
        self.tabs.addTab(self.tab_extra, "ДОПОЛНИТЕЛЬНО")
        self._build_extra_tab(self.tab_extra)

        self.tab_scenarios = QWidget()
        self.tabs.addTab(self.tab_scenarios, "СЦЕНАРИИ")
        self._build_scenarios_tab(self.tab_scenarios)

        self.tab_guide = QWidget()
        self.tabs.addTab(self.tab_guide, "СПРАВКА И ФОРМУЛЫ")
        self._build_guide_tab(self.tab_guide)

    def _build_oes_tab(self, parent):
        main_v = QVBoxLayout(parent)
        main_v.setContentsMargins(6, 6, 6, 6)
        main_v.setSpacing(6)

        upper_h = QHBoxLayout()
        upper_h.setSpacing(8)

        bezel = QFrame()
        bezel.setObjectName("BezelFrame")
        bezel_layout = QVBoxLayout(bezel)
        bezel_layout.setContentsMargins(6, 6, 6, 6)
        self.thermal_widget = ThermalMonitorWidget()
        bezel_layout.addWidget(self.thermal_widget)
        upper_h.addWidget(bezel, stretch=4)

        right_side_v = QVBoxLayout()
        right_side_v.setSpacing(5)

        self.oes_sector_widget = OesSectorSideWidget()
        right_side_v.addWidget(self.oes_sector_widget, stretch=2)

        self.oes_table = QTableWidget(6, 2)
        self.oes_table.setHorizontalHeaderLabels(["ПАРАМЕТР", "ЗНАЧЕНИЕ"])
        self.oes_table.verticalHeader().setVisible(False)
        self.oes_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        self.oes_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        param_names = ["ДАЛЬНОСТЬ", "АЗИМУТ", "УГОЛ МЕСТА", "СКОРОСТЬ", "ЗАХВАТ ОЭС", "ЗУМ / ШУМ"]
        for r_i, p_name in enumerate(param_names):
            it0 = QTableWidgetItem(p_name)
            it0.setFlags(it0.flags() & ~Qt.ItemFlag.ItemIsEditable)
            it1 = QTableWidgetItem("—")
            it1.setFlags(it1.flags() & ~Qt.ItemFlag.ItemIsEditable)
            self.oes_table.setItem(r_i, 0, it0)
            self.oes_table.setItem(r_i, 1, it1)
        right_side_v.addWidget(self.oes_table, stretch=2)

        combat_box = QFrame()
        combat_box.setObjectName("PanelBlock")
        cb_l = QVBoxLayout(combat_box)
        cb_l.setContentsMargins(6, 5, 6, 5)
        cb_l.setSpacing(4)

        cb_title = QLabel("БОЕВОЙ ПУЛЬТ (2А38М / 95Я6)")
        cb_title.setStyleSheet("background-color: #b0bec5; padding: 2px 4px; font-weight: bold;")
        cb_l.addWidget(cb_title)

        sel_w_row = QHBoxLayout()
        self.btn_sel_gun = QPushButton("ТИП: 2А38М (30мм)")
        self.btn_sel_gun.setCheckable(True)
        self.btn_sel_gun.setChecked(True)
        self.btn_sel_gun.clicked.connect(lambda: self._select_weapon_type("GUN"))
        sel_w_row.addWidget(self.btn_sel_gun)

        self.btn_sel_sam = QPushButton("ТИП: ЗУР 95Я6")
        self.btn_sel_sam.setCheckable(True)
        self.btn_sel_sam.clicked.connect(lambda: self._select_weapon_type("SAM"))
        sel_w_row.addWidget(self.btn_sel_sam)
        cb_l.addLayout(sel_w_row)

        fire_row = QHBoxLayout()
        self.btn_fire_gun = QPushButton("ОГОНЬ 2А38М\n(УДЕРЖ. ЛКМ)")
        self.btn_fire_gun.setMinimumHeight(42)
        self.btn_fire_gun.setStyleSheet(
            "QPushButton { background-color: #ffe082; color: #111; border: 2px solid #ef6c00; font-weight: bold; }"
            "QPushButton:pressed { background-color: #ff6d00; color: #fff; }"
            "QPushButton:disabled { background-color: #90a4ae; color: #37474f; border: 1px solid #546e7a; }"
        )
        self.btn_fire_gun.pressed.connect(self._on_gun_pressed)
        self.btn_fire_gun.released.connect(self._on_gun_released)
        fire_row.addWidget(self.btn_fire_gun)

        self.btn_launch_sam = QPushButton("ПУСК ЗУР 95Я6\n(ОДИНОЧНЫЙ)")
        self.btn_launch_sam.setMinimumHeight(42)
        self.btn_launch_sam.setStyleSheet(
            "QPushButton { background-color: #ffcdd2; color: #111; border: 2px solid #c62828; font-weight: bold; }"
            "QPushButton:pressed { background-color: #d50000; color: #fff; }"
            "QPushButton:disabled { background-color: #90a4ae; color: #37474f; border: 1px solid #546e7a; }"
        )
        self.btn_launch_sam.clicked.connect(self._on_sam_launch_clicked)
        fire_row.addWidget(self.btn_launch_sam)
        cb_l.addLayout(fire_row)

        self.lbl_ammo_status = QLabel("БК 2А38М: 1404 (лента 351) | ЗУР 95Я6: 12")
        self.lbl_ammo_status.setStyleSheet("font-size: 10.5px; font-weight: bold;")
        cb_l.addWidget(self.lbl_ammo_status)

        temp_row = QHBoxLayout()
        self.lbl_gun_temp = QLabel("T СТВОЛОВ: 20°C [НОРМА]")
        self.lbl_gun_temp.setStyleSheet("font-size: 10.5px; font-weight: bold;")
        temp_row.addWidget(self.lbl_gun_temp)
        cb_l.addLayout(temp_row)

        self.bar_gun_temp = QProgressBar()
        self.bar_gun_temp.setRange(20, int(TEMP_CRIT))
        self.bar_gun_temp.setValue(20)
        self.bar_gun_temp.setTextVisible(False)
        self.bar_gun_temp.setFixedHeight(10)
        cb_l.addWidget(self.bar_gun_temp)

        self.lbl_channels_detail = QLabel("КАНАЛЫ: РК 0/3 | SACLOS 0/1 | ОЭС 0/1 | НАПР: 0/2")
        self.lbl_channels_detail.setStyleSheet("font-size: 10px; color: #1a237e;")
        cb_l.addWidget(self.lbl_channels_detail)

        right_side_v.addWidget(combat_box, stretch=0)

        upper_h.addLayout(right_side_v, stretch=2)
        main_v.addLayout(upper_h, stretch=5)

        bottom_bar = QFrame()
        bottom_bar.setObjectName("OliveBar")
        bottom_bar.setMaximumHeight(155)
        bottom_h = QHBoxLayout(bottom_bar)
        bottom_h.setContentsMargins(8, 5, 8, 5)
        bottom_h.setSpacing(10)

        left_ctrl = QGridLayout()
        left_ctrl.setSpacing(4)

        left_ctrl.addWidget(QLabel("ЦЕЛЬ:"), 0, 0)
        self.combo_oes_target = QComboBox()
        for t in self.targets:
            self.combo_oes_target.addItem(f"Ц{t.id} — {t.name}")
        self.combo_oes_target.currentIndexChanged.connect(self._sync_target_selection_from_oes)
        left_ctrl.addWidget(self.combo_oes_target, 0, 1, 1, 2)

        self.btn_whot = QPushButton("WHOT")
        self.btn_whot.setCheckable(True)
        self.btn_whot.setChecked(True)
        self.btn_whot.clicked.connect(lambda: self._set_polarity("WHOT"))
        left_ctrl.addWidget(self.btn_whot, 1, 0)

        self.btn_bhot = QPushButton("BHOT")
        self.btn_bhot.setCheckable(True)
        self.btn_bhot.clicked.connect(lambda: self._set_polarity("BHOT"))
        left_ctrl.addWidget(self.btn_bhot, 1, 1)

        self.btn_green = QPushButton("ЛЮМ")
        self.btn_green.setCheckable(True)
        self.btn_green.clicked.connect(lambda: self._set_polarity("GREEN"))
        left_ctrl.addWidget(self.btn_green, 1, 2)

        self.btn_z1 = QPushButton("x1")
        self.btn_z1.setCheckable(True)
        self.btn_z1.setChecked(True)
        self.btn_z1.clicked.connect(lambda: self._set_zoom(1))
        left_ctrl.addWidget(self.btn_z1, 2, 0)

        self.btn_z2 = QPushButton("x2")
        self.btn_z2.setCheckable(True)
        self.btn_z2.clicked.connect(lambda: self._set_zoom(2))
        left_ctrl.addWidget(self.btn_z2, 2, 1)

        self.btn_z4 = QPushButton("x4")
        self.btn_z4.setCheckable(True)
        self.btn_z4.clicked.connect(lambda: self._set_zoom(4))
        left_ctrl.addWidget(self.btn_z4, 2, 2)

        bottom_h.addLayout(left_ctrl, stretch=2)

        mid_ctrl = QGridLayout()
        mid_ctrl.setSpacing(4)

        self.btn_auto_track = QPushButton("АВТОСОПР: ВКЛ")
        self.btn_auto_track.setCheckable(True)
        self.btn_auto_track.setChecked(True)
        self.btn_auto_track.clicked.connect(self._toggle_auto_track)
        mid_ctrl.addWidget(self.btn_auto_track, 0, 0, 1, 2)

        self.lbl_manual_az = QLabel("АЗМ: 35°")
        mid_ctrl.addWidget(self.lbl_manual_az, 1, 0)
        self.slider_cam_az = QSlider(Qt.Orientation.Horizontal)
        self.slider_cam_az.setRange(0, 359)
        self.slider_cam_az.setValue(35)
        self.slider_cam_az.valueChanged.connect(self._on_manual_cam_change)
        mid_ctrl.addWidget(self.slider_cam_az, 1, 1)

        self.lbl_manual_el = QLabel("УМ: 15°")
        mid_ctrl.addWidget(self.lbl_manual_el, 2, 0)
        self.slider_cam_el = QSlider(Qt.Orientation.Horizontal)
        self.slider_cam_el.setRange(0, 65)
        self.slider_cam_el.setValue(15)
        self.slider_cam_el.valueChanged.connect(self._on_manual_cam_change)
        mid_ctrl.addWidget(self.slider_cam_el, 2, 1)

        bottom_h.addLayout(mid_ctrl, stretch=2)

        right_ctrl = QVBoxLayout()
        right_ctrl.setSpacing(4)

        self.lbl_oes_lock_badge = QLabel(" ЗАХВАТ: АКТИВЕН ")
        self.lbl_oes_lock_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.lbl_oes_lock_badge.setStyleSheet(
            "background-color: #76ff03; color: #000; font-weight: bold; padding: 4px;"
        )
        right_ctrl.addWidget(self.lbl_oes_lock_badge)

        self.lbl_oes_card = QLabel("ОЭС ГОТОВА")
        self.lbl_oes_card.setStyleSheet(
            "background-color: #eceff1; border: 1px solid #455a64; padding: 4px; font-size: 10.5px;"
        )
        self.lbl_oes_card.setWordWrap(True)
        right_ctrl.addWidget(self.lbl_oes_card)

        btn_to_radar = QPushButton("МОНИТОР 2 (РЛС) ->")
        btn_to_radar.clicked.connect(lambda: self.tabs.setCurrentIndex(1))
        right_ctrl.addWidget(btn_to_radar)

        bottom_h.addLayout(right_ctrl, stretch=2)
        main_v.addWidget(bottom_bar, stretch=0)

    def _build_radar_tab(self, parent):
        layout = QHBoxLayout(parent)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(10)

        bezel = QFrame()
        bezel.setObjectName("BezelFrame")
        bezel_layout = QVBoxLayout(bezel)
        bezel_layout.setContentsMargins(10, 10, 10, 10)
        self.radar_widget = TacticalRadarWidget()
        bezel_layout.addWidget(self.radar_widget)
        layout.addWidget(bezel, stretch=3)

        right_panel = QFrame()
        right_panel.setObjectName("PanelBlock")
        right_layout = QVBoxLayout(right_panel)
        right_layout.setSpacing(6)

        r_title = QLabel("ПУЛЬТ УПРАВЛЕНИЯ РЛК (СОЦ / ССЦ)")
        r_title.setStyleSheet("background-color: #b0bec5; padding: 4px; font-weight: bold;")
        right_layout.addWidget(r_title)

        btn_grid = QGridLayout()
        self.btn_r_pause = QPushButton("ПУСК / ПАУЗА")
        self.btn_r_pause.clicked.connect(self._toggle_run)
        btn_grid.addWidget(self.btn_r_pause, 0, 0)

        self.btn_r_mode = QPushButton("РЕЖИМ: КРУГ 360°")
        self.btn_r_mode.setCheckable(True)
        self.btn_r_mode.clicked.connect(self._toggle_sector_mode)
        btn_grid.addWidget(self.btn_r_mode, 0, 1)

        self.btn_r_freq = QPushButton("ЧАСТОТА: 3.0 ГГц (S)")
        self.btn_r_freq.clicked.connect(self._cycle_freq)
        btn_grid.addWidget(self.btn_r_freq, 1, 0)

        self.btn_r_add = QPushButton("+ ДОБАВИТЬ ЦЕЛЬ")
        self.btn_r_add.clicked.connect(self._add_random_target)
        btn_grid.addWidget(self.btn_r_add, 1, 1)

        self.btn_r_maneuver = QPushButton("МАНЁВР 3/9 (В ТРАВЕРЗ)")
        self.btn_r_maneuver.clicked.connect(self._trigger_beam_maneuver)
        btn_grid.addWidget(self.btn_r_maneuver, 2, 0)

        self.btn_r_reset = QPushButton("СБРОС ОБСТАНОВКИ")
        self.btn_r_reset.clicked.connect(self._reset_sim)
        btn_grid.addWidget(self.btn_r_reset, 2, 1)
        right_layout.addLayout(btn_grid)

        sel_row = QHBoxLayout()
        sel_row.addWidget(QLabel("Захват цели:"))
        self.combo_radar_target = QComboBox()
        for t in self.targets:
            self.combo_radar_target.addItem(f"Ц{t.id} — {t.name}")
        self.combo_radar_target.currentIndexChanged.connect(self._sync_target_selection_from_radar)
        sel_row.addWidget(self.combo_radar_target, stretch=1)
        right_layout.addLayout(sel_row)

        self.btn_threat_jump = QPushButton("НЕТ УГРОЗ В ВОЗДУХЕ")
        self.btn_threat_jump.setEnabled(False)
        self.btn_threat_jump.setStyleSheet(
            "QPushButton:enabled { background-color: #ff1744; color: #fff; border: 1px solid #b71c1c; font-weight: bold; }"
        )
        self.btn_threat_jump.clicked.connect(self._jump_to_latest_threat)
        right_layout.addWidget(self.btn_threat_jump)

        self.lbl_r_noise = QLabel("Помеховая обстановка: 22%")
        right_layout.addWidget(self.lbl_r_noise)
        self.slider_r_noise = QSlider(Qt.Orientation.Horizontal)
        self.slider_r_noise.setRange(0, 100)
        self.slider_r_noise.setValue(22)
        self.slider_r_noise.valueChanged.connect(self._on_r_noise_change)
        right_layout.addWidget(self.slider_r_noise)

        self.btn_no_lock_scan = QPushButton("РЕЖИМ: СКАН БЕЗ ЗАХВАТА (ВЫКЛ)")
        self.btn_no_lock_scan.setCheckable(True)
        self.btn_no_lock_scan.clicked.connect(self._toggle_no_lock_scan)
        right_layout.addWidget(self.btn_no_lock_scan)

        self.btn_arc180_mode = QPushButton("ЗОНА 180° (ДОПЛЕР/ОБЗОР): ВЫКЛ")
        self.btn_arc180_mode.setCheckable(True)
        self.btn_arc180_mode.clicked.connect(self._toggle_arc180_mode)
        right_layout.addWidget(self.btn_arc180_mode)

        self.btn_sector_follow = QPushButton("СЕКТОР 90° ЗА ЦЕЛЬЮ: ВКЛ")
        self.btn_sector_follow.setCheckable(True)
        self.btn_sector_follow.setChecked(True)
        self.btn_sector_follow.clicked.connect(self._toggle_sector_follow)
        right_layout.addWidget(self.btn_sector_follow)

        self.lbl_r_sec = QLabel("Центр сектора обзора: 35°")
        right_layout.addWidget(self.lbl_r_sec)
        self.slider_r_sec = QSlider(Qt.Orientation.Horizontal)
        self.slider_r_sec.setRange(0, 359)
        self.slider_r_sec.setValue(35)
        self.slider_r_sec.valueChanged.connect(self._on_sector_center_change)
        right_layout.addWidget(self.slider_r_sec)

        self.lbl_radar_card = QLabel("Формуляр цели: —")
        self.lbl_radar_card.setStyleSheet(
            "background-color: #eceff1; border: 1px solid #90a4ae; padding: 7px; font-size: 11.5px;"
        )
        self.lbl_radar_card.setWordWrap(True)
        right_layout.addWidget(self.lbl_radar_card)

        log_hdr_row = QHBoxLayout()
        lbl_log_title = QLabel("ЖУРНАЛ СОБЫТИЙ РЛК / ОЭС:")
        lbl_log_title.setStyleSheet("font-weight: bold; color: #1b2631;")
        log_hdr_row.addWidget(lbl_log_title)
        log_hdr_row.addStretch(1)
        btn_clear_log = QPushButton("ОЧИСТИТЬ")
        btn_clear_log.setFixedHeight(20)
        btn_clear_log.clicked.connect(self._clear_event_log)
        log_hdr_row.addWidget(btn_clear_log)
        right_layout.addLayout(log_hdr_row)

        self.txt_event_log = QTextEdit()
        self.txt_event_log.setReadOnly(True)
        self.txt_event_log.setMinimumHeight(120)
        self.txt_event_log.setStyleSheet(
            "background-color: #101820; color: #b9f6ca; border: 1px solid #455a64; "
            "font-family: Consolas, monospace; font-size: 10.5px; padding: 4px;"
        )
        right_layout.addWidget(self.txt_event_log, stretch=1)

        btn_to_oes = QPushButton("<- ПЕРЕЙТИ НА МОНИТОР 1 (ОЭС / ТЕПЛАК)")
        btn_to_oes.clicked.connect(lambda: self.tabs.setCurrentIndex(0))
        right_layout.addWidget(btn_to_oes)

        layout.addWidget(right_panel, stretch=2)

    def _build_extra_tab(self, parent):
        layout = QHBoxLayout(parent)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(10)

        plots_col = QVBoxLayout()
        plots_col.setSpacing(8)
        self.plot_ascope = JammingPlotWidget("ascope")
        self.plot_doppler = JammingPlotWidget("doppler")
        for w in (self.plot_ascope, self.plot_doppler):
            bezel = QFrame()
            bezel.setObjectName("BezelFrame")
            bl = QVBoxLayout(bezel)
            bl.setContentsMargins(6, 6, 6, 6)
            bl.addWidget(w)
            plots_col.addWidget(bezel, stretch=1)
        layout.addLayout(plots_col, stretch=3)

        right_panel = QFrame()
        right_panel.setObjectName("PanelBlock")
        rl = QVBoxLayout(right_panel)
        rl.setSpacing(7)

        title = QLabel("ПОМЕХОВАЯ ОБСТАНОВКА, ЗВУК И ПАРАМЕТРЫ БОЯ")
        title.setStyleSheet("background-color: #b0bec5; padding: 4px; font-weight: bold;")
        rl.addWidget(title)

        opts_row = QHBoxLayout()
        self.btn_sound_toggle = QPushButton("ЗВУК: ВКЛ")
        self.btn_sound_toggle.setCheckable(True)
        self.btn_sound_toggle.setChecked(True)
        self.btn_sound_toggle.clicked.connect(self._toggle_sound)
        opts_row.addWidget(self.btn_sound_toggle)

        btn_test_snd = QPushButton("ТЕСТ ЗВУКА / ТРЕВОГИ")
        btn_test_snd.clicked.connect(self._test_audio_signals)
        opts_row.addWidget(btn_test_snd)

        self.btn_range_limit_toggle = QPushButton("ОГРАН. 2А38М > 5 КМ: ВКЛ")
        self.btn_range_limit_toggle.setCheckable(True)
        self.btn_range_limit_toggle.setChecked(True)
        self.btn_range_limit_toggle.clicked.connect(self._toggle_gun_range_limit)
        opts_row.addWidget(self.btn_range_limit_toggle)
        rl.addLayout(opts_row)

        vol_row = QHBoxLayout()
        self.lbl_sound_vol = QLabel("Громкость звука: 80%")
        vol_row.addWidget(self.lbl_sound_vol)
        self.slider_sound_vol = QSlider(Qt.Orientation.Horizontal)
        self.slider_sound_vol.setRange(0, 100)
        self.slider_sound_vol.setValue(80)
        self.slider_sound_vol.valueChanged.connect(self._on_sound_volume_change)
        vol_row.addWidget(self.slider_sound_vol, stretch=1)
        rl.addLayout(vol_row)

        self.lbl_audio_diag = QLabel(f"Аудио-бэкенд: {self.sound_engine._backend or 'не найден (тихий режим)'}")
        self.lbl_audio_diag.setStyleSheet("font-size: 10px; color: #37474f;")
        rl.addWidget(self.lbl_audio_diag)

        self.lbl_x_noise = QLabel("Помеховая обстановка: 22%")
        rl.addWidget(self.lbl_x_noise)
        self.slider_x_noise = QSlider(Qt.Orientation.Horizontal)
        self.slider_x_noise.setRange(0, 100)
        self.slider_x_noise.setValue(22)
        self.slider_x_noise.valueChanged.connect(self._on_extra_noise_change)
        rl.addWidget(self.slider_x_noise)

        self.lbl_x_formulas = QLabel("—")
        self.lbl_x_formulas.setTextFormat(Qt.TextFormat.RichText)
        self.lbl_x_formulas.setWordWrap(True)
        self.lbl_x_formulas.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.lbl_x_formulas.setStyleSheet(
            "background-color: #eceff1; border: 1px solid #90a4ae; padding: 8px; font-size: 12px;"
        )
        rl.addWidget(self.lbl_x_formulas, stretch=1)

        btn_back = QPushButton("<- ПЕРЕЙТИ НА МОНИТОР 2 (РЛС)")
        btn_back.clicked.connect(lambda: self.tabs.setCurrentIndex(1))
        rl.addWidget(btn_back)

        layout.addWidget(right_panel, stretch=2)

    def _test_audio_signals(self):
        self.sound_engine.play_gun_shot(self.sim_time_sec + 1.0)
        QTimer.singleShot(220, lambda: self.sound_engine.play_alarm(self.sim_time_sec + 2.0))
        self._log_event(f"Проверка звука (бэкенд: {self.sound_engine._backend or 'нет'})", "INFO")

    def _on_sound_volume_change(self, val):
        try:
            self.sound_engine.set_volume(val / 100.0)
            if hasattr(self, "lbl_sound_vol"):
                self.lbl_sound_vol.setText(f"Громкость звука: {val}%")
        except Exception as exc:
            _log_py_err("_on_sound_volume_change", exc)

    def _toggle_sound(self):
        try:
            st = bool(self.btn_sound_toggle.isChecked())
            self.sound_engine.enabled = st
            self.btn_sound_toggle.setText(f"ЗВУК: {'ВКЛ' if st else 'ВЫКЛ'}")
        except Exception as exc:
            _log_py_err("_toggle_sound", exc)

    def _toggle_gun_range_limit(self):
        try:
            st = bool(self.btn_range_limit_toggle.isChecked())
            self.gun_range_limit_enabled = st
            self.btn_range_limit_toggle.setText(f"ОГРАН. 2А38М > 5 КМ: {'ВКЛ' if st else 'ВЫКЛ'}")
            self._log_event(
                f"Ограничение дальности автопушек (> 5 км) {'включено' if st else 'отключено оператором'}",
                "INFO"
            )
        except Exception as exc:
            _log_py_err("_toggle_gun_range_limit", exc)

    def _select_weapon_type(self, wtype):
        self.selected_weapon = wtype
        self.btn_sel_gun.setChecked(wtype == "GUN")
        self.btn_sel_sam.setChecked(wtype == "SAM")

    def _get_selected_target(self):
        idx = self.combo_radar_target.currentIndex()
        if 0 <= idx < len(self.targets):
            return self.targets[idx]
        return None

    def _on_gun_pressed(self):
        self._select_weapon_type("GUN")
        self.gun_trigger_held = True

    def _on_gun_released(self):
        self.gun_trigger_held = False

    def _get_channel_counts(self):
        rk_cnt = sum(1 for v in self.channel_assignments.values() if v["mode"] == "РК")
        saclos_cnt = sum(1 for v in self.channel_assignments.values() if v["mode"] == "SACLOS")
        oes_cnt = sum(1 for v in self.channel_assignments.values() if v["mode"] == "ОЭС")
        dir_cnt = sum(1 for v in self.channel_assignments.values() if v["directed"])
        return rk_cnt, saclos_cnt, oes_cnt, dir_cnt

    def _assign_guidance_channel(self, target_id):
        if target_id in self.channel_assignments:
            return self.channel_assignments[target_id]
        rk_cnt, saclos_cnt, oes_cnt, dir_cnt = self._get_channel_counts()
        if rk_cnt < 3:
            info = {"mode": "РК", "directed": False}
        elif saclos_cnt < 1 and dir_cnt < 2:
            info = {"mode": "SACLOS", "directed": True}
        elif oes_cnt < 1 and dir_cnt < 2:
            info = {"mode": "ОЭС", "directed": True}
        else:
            return None
        self.channel_assignments[target_id] = info
        return info

    def _release_channel_if_unused(self, target_id):
        still_used = any(s.active and s.target_id == target_id for s in self.active_sams)
        if not still_used and target_id in self.channel_assignments:
            del self.channel_assignments[target_id]

    def _on_sam_launch_clicked(self):
        self._select_weapon_type("SAM")
        if not self.suo_powered:
            self._log_event("Пуск ЗУР невозможен: СУО отключена", "WARN")
            return
        if not self.combat_mode:
            self._log_event("Пуск ЗУР доступен в боевом режиме (вкладка «Сценарии» -> 6. Боевой режим)", "WARN")
            return
        if self.sam_ammo <= 0:
            self._log_event("БК ЗУР 95Я6 ИСЧЕРПАН (0/12)", "WARN")
            return
        if self.sam_cooldown > 0.0:
            self._log_event(f"Подготовка пусковой 95Я6: готовность через {self.sam_cooldown:.1f} с", "WARN")
            return
        t = self._get_selected_target()
        if t is None or not t.alive or self.no_lock_scan:
            self._log_event("Нет захваченной цели для пуска ЗУР 95Я6", "WARN")
            return
        r_km, az, el = t.polar()
        if r_km > SAM_MAX_RANGE_KM:
            self._log_event(f"Ц{t.id} вне зоны пуска ЗУР 95Я6 (Д={r_km:.1f} км > 20.0 км)", "WARN")
            return

        ch = self._assign_guidance_channel(t.id)
        if ch is None:
            self._log_event("ВСЕ 5 КАНАЛОВ НАВЕДЕНИЯ ЗАНЯТЫ (3 РК + 1 SACLOS + 1 ОЭС, 2 НАПРАВЛЕННЫХ)!", "WARN")
            return

        self.sam_ammo -= 1
        self.sam_cooldown = SAM_FIRE_INTERVAL
        sam = ActiveSamProjectile(self.next_sam_id, t.id, ch["mode"], ch["directed"], az, el)
        self.next_sam_id += 1
        self.active_sams.append(sam)
        self.sound_engine.play_sam_launch()

        dir_tag = " [НАПРАВЛЕННЫЙ]" if ch["directed"] else ""
        self._log_event(
            f"ПУСК ЗУР 95Я6 #{sam.id} ПО Ц{t.id} ({t.name}) | КАНАЛ: {ch['mode']}{dir_tag} | ОСТАТОК ЗУР: {self.sam_ammo}",
            "INFO"
        )
        if t.under_fire_react_cd <= 0.0:
            t.trigger_defensive_maneuver(force_notch=(random.random() < 0.35))
            t.under_fire_react_cd = 4.0
            self._log_event(f"Ц{t.id}: зафиксирован уход в контрманёвр!", "WARN")

    def _compute_gun_lead_angles(self, target):
        r_km, _, _ = target.polar()
        tof = (r_km * 1000.0) / GUN_MUZZLE_VEL_MS
        pred_x = target.x + (target.vx / 1000.0) * tof
        pred_y = target.y + (target.vy / 1000.0) * tof
        pred_alt = target.alt
        r_h = math.hypot(pred_x, pred_y)
        aim_az = math.degrees(math.atan2(pred_x, pred_y)) % 360.0
        drop_km = 0.5 * 9.81 * (tof ** 2) / 1000.0
        aim_el = math.degrees(math.atan2(pred_alt + drop_km, max(0.05, r_h)))
        return aim_az, aim_el, tof

    def _process_gun_firing_step(self, dt_real):
        self.gun_temp += -TEMP_COOL_K * (self.gun_temp - TEMP_AMBIENT) * dt_real
        if self.gun_temp < TEMP_AMBIENT:
            self.gun_temp = TEMP_AMBIENT

        if not self.gun_trigger_held:
            self.gun_shot_accum = 0.0
            return

        if not self.suo_powered or not self.combat_mode:
            return
        if self.gun_jammed:
            return
        if self.gun_ammo <= 0:
            self.gun_trigger_held = False
            self._log_event("БК АВТОПУШЕК 2А38М ИСЧЕРПАН (0/1404)", "WARN")
            return

        t = self._get_selected_target()
        if t is None or not t.alive or self.no_lock_scan:
            return

        r_km, _az, _el = t.polar()
        if self.gun_range_limit_enabled and r_km > GUN_DEFAULT_RANGE_LIMIT_KM:
            return

        self.gun_shot_accum += dt_real
        shots_this_tick = 0
        while self.gun_shot_accum >= GUN_SHOT_INTERVAL and self.gun_ammo > 0 and not self.gun_jammed:
            self.gun_shot_accum -= GUN_SHOT_INTERVAL
            self.gun_ammo -= 1
            self.gun_temp += TEMP_PER_SHOT
            shots_this_tick += 1

            if self.gun_temp >= TEMP_CRIT:
                self.gun_temp = TEMP_CRIT
                self.gun_jammed = True
                self.gun_trigger_held = False
                self.sound_engine.play_jam()
                self._log_event(
                    f"КРИТИЧЕСКИЙ ПЕРЕГРЕВ 2А38М ({self.gun_temp:.0f}°C) — КЛИН СТВОЛОВ! ТРЕБУЕТСЯ ПЕРЕЗАПУСК СЦЕНАРИЯ",
                    "WARN"
                )
                break
            elif self.gun_temp >= TEMP_WARN:
                e_ratio = (self.gun_temp - TEMP_WARN) / (TEMP_CRIT - TEMP_WARN)
                p_jam = 0.018 * (e_ratio ** 2)
                if random.random() < p_jam:
                    self.gun_jammed = True
                    self.gun_trigger_held = False
                    self.sound_engine.play_jam()
                    self._log_event(
                        f"ТЕПЛОВОЙ КЛИН АВТОПУШЕК 2А38М ПРИ {self.gun_temp:.0f}°C! СТВОЛЫ ЗАБЛОКИРОВАНЫ ДО ПЕРЕЗАПУСКА",
                        "WARN"
                    )
                    break

        if shots_this_tick > 0:
            self.sound_engine.play_gun_shot(self.sim_time_sec)
            aim_az, aim_el, _ = self._compute_gun_lead_angles(t)
            start_az = (self.cam_az + random.uniform(-0.8, 0.8)) % 360.0
            start_el = max(0.0, self.cam_el - 3.2 + random.uniform(-0.4, 0.4))
            hit_prob = max(0.18, min(0.88, 1.0 - (r_km / 6.2) * 0.65))
            will_hit = (random.random() < hit_prob)
            self.active_tracers.append(
                GunTracerBurst(start_az, start_el, aim_az, aim_el, r_km, hit_will_occur=will_hit)
            )
            if t.under_fire_react_cd <= 0.0:
                t.trigger_defensive_maneuver(force_notch=False)
                t.under_fire_react_cd = 3.5

    def _spawn_enemy_ordnance(self, attacker):
        if not attacker.ordnance:
            return
        mun_name = random.choice(attacker.ordnance)
        nid = self.next_target_id
        self.next_target_id += 1
        r_km, _, _ = attacker.polar()
        spd = random.uniform(360.0, 540.0)
        vx = -(attacker.x / max(0.1, r_km)) * spd
        vy = -(attacker.y / max(0.1, r_km)) * spd
        mun = SimTarget(
            nid, f"{mun_name} [от Ц{attacker.id}]", "missile",
            attacker.x, attacker.y, attacker.alt, vx, vy,
            rcs=0.35, ordnance_list=[], is_munitions=True, parent_id=attacker.id,
            max_out_km=MAX_RANGE_KM + COMBAT_EXTRA_OUT_KM
        )
        self.targets.append(mun)
        self.combo_oes_target.addItem(f"Ц{mun.id} — {mun.name}")
        self.combo_radar_target.addItem(f"Ц{mun.id} — {mun.name}")
        self.latest_threat_target_id = mun.id
        if hasattr(self, "btn_threat_jump"):
            self.btn_threat_jump.setEnabled(True)
            self.btn_threat_jump.setText(f"! ПЕРЕКЛЮЧИТЬ ПРИОРИТЕТ НА Ц{mun.id}: {mun_name} !")

        self.sound_engine.play_alarm(self.sim_time_sec)
        self._log_event(
            f"ВНИМАНИЕ! ЗАСЕЧЁН ОТВЕТНЫЙ ПУСК ОТ Ц{attacker.id}: {mun_name.upper()} (Д={r_km:.1f} КМ) — Ц{mun.id}!",
            "WARN"
        )

    def _jump_to_latest_threat(self):
        if self.latest_threat_target_id is None:
            return
        for idx, t in enumerate(self.targets):
            if t.id == self.latest_threat_target_id and t.alive:
                self.combo_radar_target.setCurrentIndex(idx)
                self.combo_oes_target.setCurrentIndex(idx)
                self.no_lock_scan = False
                self.btn_no_lock_scan.setChecked(False)
                self.btn_no_lock_scan.setText("РЕЖИМ: СКАН БЕЗ ЗАХВАТА (ВЫКЛ)")
                self.tabs.setCurrentIndex(0)
                self._log_event(f"ПРИОРИТЕТ ПЕРЕВЕДЁН НА ПОДЛЕТАЮЩИЙ БОЕПРИПАС Ц{t.id} ({t.name})", "WARN")
                return

    def _return_to_initial_non_combat(self):
        self.combat_mode = False
        self.lbl_mode_badge.setText(" РЕЖИМ: УЧЕБНЫЙ ")
        self.lbl_mode_badge.setStyleSheet("background-color: #b0bec5; color: #000; font-weight: bold; padding: 2px 6px;")
        self._reset_combat_systems()
        self._apply_scenario("standard")
        self._apply_suo_power_state(False)
        self._log_event("Выполнен возврат к началу: не боевой режим, СУО выключена", "WARN")

    def _on_extra_noise_change(self, val):
        self.slider_r_noise.setValue(val)

    def _update_extra_tab(self):
        powered = bool(getattr(self, "suo_powered", False))
        self.plot_ascope.set_powered(powered)
        self.plot_doppler.set_powered(powered)
        if not powered:
            self.lbl_x_formulas.setText(
                "<b>СУО ОТКЛЮЧЕНА</b><br><br>"
                "РЛС не излучает и не принимает, эхо-сигналов нет: "
                "А-развёртка и доплеровский спектр не строятся, расчёты недоступны."
            )
            return
        thr = detection_threshold(self.noise_level)
        sel_idx = self.combo_radar_target.currentIndex()
        items = []
        sel = None
        sel_t = None
        sel_r = 0.0
        sel_out = False
        half_sec = self.sector_width * 0.5
        half_zone = self.radar_widget.arc180_width * 0.5
        out_txt = "ВНЕ СЕКТОРА ОБЗОРА 90°"
        for idx, t in enumerate(self.targets):
            if not t.alive:
                continue
            r_slant, az, _el = t.polar()
            in_90 = (not self.sector_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_sec)
            in_zone = (not self.arc180_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_zone)
            in_sec = in_90 and in_zone
            is_sel = (idx == sel_idx)
            if is_sel:
                sel_t, sel_r = t, r_slant
            if not in_sec:
                if is_sel:
                    sel_out = True
                    out_txt = "ВНЕ СЕКТОРА ОБЗОРА 90°" if not in_90 else "ВНЕ ЗОНЫ 180°"
                continue
            amp = (t.rcs * 11.5) / max(1.5, r_slant)
            vr_t = t.radial_vel()
            notched = abs(vr_t) < NOTCH_VR_MS
            det = bool(amp > thr) and not notched
            amp_disp = amp * 0.08 if notched else amp
            items.append((t.id, r_slant, amp_disp, det, is_sel, notched))
            if is_sel:
                sel = (t.doppler_khz(self.f0_ghz), amp, vr_t, bool(amp > thr))

        note = f"ЦЕЛЬ {out_txt}" if sel_out else ""
        self.plot_ascope.set_data(self.noise_level, self.f0_ghz, items, sel)
        self.plot_doppler.set_data(self.noise_level, self.f0_ghz, items, sel, note)

        if sel_t is None or not sel_t.alive:
            self.lbl_x_formulas.setText("Активная цель не выбрана.")
            return
        if sel_out:
            self.lbl_x_formulas.setText(
                f"<b>Цель №{sel_t.id}: {sel_t.name}</b><br><br>"
                f"<b>{out_txt}</b><br>"
                "Эхо-сигнал не принимается, на графиках цель не отображается."
            )
            return
        fd, _amp, vr, _det = sel
        delay_us = 2.0 * sel_r * 1000.0 / C * 1e6
        _, _, gun_tof = self._compute_gun_lead_angles(sel_t)
        self.lbl_x_formulas.setText(
            f"<b>Цель №{sel_t.id}: {sel_t.name}</b><br>"
            f"Подвес цели: {', '.join(sel_t.ordnance) if sel_t.ordnance else 'нет ударного подвеса'}<br><br>"
            f"<b>1. Задержка эхо-сигнала:</b> t = {delay_us:.1f} мкс<br>"
            f"<b>2. Радиальная скорость / Доплер:</b> Vr = {vr:+.1f} м/с | fd = {fd:+.2f} кГц<br>"
            f"<b>3. Упреждение 2А38М (960 м/с):</b> подлёт снарядов {gun_tof:.2f} с<br>"
            f"<b>4. Тепловой режим стволов:</b> T = {self.gun_temp:.1f}°C (риск &gt; 350°C, клин 680°C)"
        )

    def _build_guide_tab(self, parent):
        layout = QVBoxLayout(parent)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        hdr = QLabel("РУКОВОДСТВО ОПЕРАТОРА: БОЕВОЙ МОДУЛЬ, КАНАЛЫ НАВЕДЕНИЯ И БАЛЛИСТИКА")
        hdr.setStyleSheet("background-color: #b0bec5; padding: 6px; font-weight: bold; font-size: 12.5px;")
        layout.addWidget(hdr)

        guide_view = QTextEdit()
        guide_view.setReadOnly(True)
        guide_view.setStyleSheet(
            "background-color: #101820; color: #e0f2f1; border: 1px solid #455a64; "
            "font-family: Consolas, monospace; font-size: 11.5px; padding: 10px;"
        )
        guide_html = """
        <h3 style="color:#69f0ae;">1. Назначение и управление</h3>
        <ul>
          <li><b>СУО: ВКЛ / ВЫКЛ</b> — общее питание каналов ОЭС и РЛС. При запуске СУО выключена. При отключении тепловизор уходит в чёрный экран, радарный индикатор очищается, в таблицах и формулярах — «СУО отключена», на вкладке «Дополнительно» гаснут А-развёртка и доплеровский спектр. Цели при этом продолжают движение.</li>
          <li><b>F11 / Esc</b> — переключение полноэкранного режима и оконного режима.</li>
          <li><b>Монитор 1 (ОЭС / Тепловизор)</b> — матрица 96×72, полярности <b>WHOT</b>, <b>BHOT</b>, <b>ЛЮМ</b>, кратность зума <b>x1 / x2 / x4</b> (при смене зума возможен кратковременный сбой изображения), <b>АВТОСОПР</b> — камера сама следит за захваченной целью, либо ручные углы азимута и угла места.</li>
          <li><b>Монитор 2 (РЛС)</b> — круговой обзор <b>360°</b> или секторный <b>90°</b>, выбор частоты, уровень помех, выбор цели, журнал событий (кнопка «Очистить»).</li>
          <li><b>Дополнительно</b> — А-развёртка (амплитуда от дальности) и доплеровский спектр выбранной цели с полосой режекции, пошаговый расчёт по выбранной цели, а также управление звуком, громкостью и ограничением дальности автопушек (&gt; 5 км). Ползунок помех синхронизирован с Монитором 2.</li>
          <li><b>Сценарии</b> — быстрая загрузка готовых тактических обстановок, настройка состава противников для боевого режима и сброс к стандартному сценарию.</li>
        </ul>

        <h3 style="color:#ffd54f;">2. Кнопки Монитора 2 (РЛС)</h3>
        <ul>
          <li><b>ПУСК / ПАУЗА</b> — останавливает и возобновляет движение целей и развёртку луча.</li>
          <li><b>РЕЖИМ: КРУГ 360° / СЕКТОР 90°</b> — круговой обзор или качание луча только в пределах сектора. Цели вне сектора не обнаруживаются.</li>
          <li><b>ЧАСТОТА</b> — по кругу переключает рабочие частоты 2.5 (S), 3.5 (S), 10 (X) и 15 (Ku) ГГц. От частоты зависит доплеровский сдвиг.</li>
          <li><b>СЕКТОР 90° ЗА ЦЕЛЬЮ</b> — центр сектора автоматически следует за захваченной целью. Ручное движение ползунка центра отключает слежение.</li>
          <li><b>ЗОНА 180° (ДОПЛЕР/ОБЗОР)</b> — ограничивает обзор полуплоскостью ±90° от центра сектора. Луч и пунктир качаются только внутри зоны (если включён сектор 90°, то внутри него), цели вне зоны не обнаруживаются, не обновляются и пропадают с индикатора (после 4 с прогноза). Границы зоны показаны розовыми линиями.</li>
          <li><b>РЕЖИМ: СКАН БЕЗ ЗАХВАТА</b> — ни одна цель не захвачена: рабочий луч и пунктирная линия вместе обзорно сканируют пространство, отметки обновляются только при проходе луча и прогнозируются между проходами. В теплаке цель не показывается.</li>
          <li><b>+ ДОБАВИТЬ ЦЕЛЬ</b> — добавляет случайную цель (истребитель или БПЛА), всего не более 16.</li>
          <li><b>МАНЁВР 3/9 (В ТРАВЕРЗ)</b> — разворачивает выбранную цель на курс, перпендикулярный линии визирования. Радиальная скорость становится близкой к нулю, и цель попадает в полосу режекции.</li>
          <li><b>СБРОС ОБСТАНОВКИ</b> — возврат к текущему/стандартному сценарию.</li>
        </ul>

        <h3 style="color:#ffd54f;">3. Захват, потеря и срыв сопровождения</h3>
        <ul>
          <li>Цель считается <b>обнаруженной</b>, если сигнал выше порога и она находится в секторе обзора. Захват удерживается только при |V<sub>r</sub>| ≥ 18 м/с: при меньшей радиальной скорости цель в полосе <b>режекции</b>, доплеровский сигнал теряется и захват сбивается.</li>
          <li>При потере цели (шумы, выход из сектора, режекция) активное сопровождение сбрасывается. В течение <b>4.0 с</b> алгоритм ведёт прогноз маршрута по последним известным параметрам движения, после чего отметка <b>плавно угасает</b> (около 1.5 с).</li>
          <li>Захваченная цель ведётся непрерывно, остальные цели обновляют данные при проходе луча или пунктира и прогнозируются между проходами.</li>
          <li>Все срывы, восстановления и снятие отметок записываются в журнал событий.</li>
          <li><b>Крупные цели.</b> Чем больше ЭПР σ, тем сильнее сигнал A относительно порога: у истребителей σ ≈ 3–5, у БПЛА около 0.6, у очень крупных целей σ на порядок выше. Такие цели помехи почти не срывают, срыв возможен в основном из-за выхода из сектора или зоны либо попадания в полосу режекции. В тепловизоре они заметно крупнее.</li>
        </ul>

        <h3 style="color:#80cbc4;">4. Основные расчётные формулы</h3>
        <p><b>Наклонная дальность и углы:</b><br>
        R<sub>гор</sub> = √(x² + y²), &nbsp; R = √(R<sub>гор</sub>² + H²), &nbsp; АЗМ = atan2(x, y), &nbsp; УМ = atan2(H, R<sub>гор</sub>)</p>
        <p><b>Время задержки эхо-сигнала:</b><br>
        t = 2 · R / c, &nbsp; где c ≈ 3·10⁸ м/с</p>
        <p><b>Радиальная скорость и доплеровский сдвиг:</b><br>
        V<sub>r</sub> = −(x·V<sub>x</sub> + y·V<sub>y</sub>) / R<sub>гор</sub>, &nbsp; f<sub>d</sub> = 2 · V<sub>r</sub> · f₀ / c</p>
        <p><b>Оценка сигнала и порога обнаружения:</b><br>
        A = σ · 11.5 / max(1.5, R), &nbsp; порог = 0.18 + (шум)<sup>1.15</sup> · 3.1 (+0.35 при шуме ≥ 70%)</p>
        <p><b>Условие захвата:</b><br>
        A &gt; порог &nbsp; и &nbsp; цель в секторе &nbsp; и &nbsp; |V<sub>r</sub>| ≥ 18 м/с</p>

        <hr style="border: 1px solid #455a64;">
        <h3 style="color:#69f0ae;">5. Боевой режим: вооружение, каналы наведения и противники</h3>
        <ul>
          <li><b>Запуск и настройка:</b> активируется во вкладке <b>«Сценарии» → «6. БОЕВОЙ РЕЖИМ»</b>. Перед запуском можно настроить число противников (1–10) и их состав (Су-30СМ, F-16C, Rafale, БПЛА).</li>
          <li><b>Дальний спавн и выход за пределы РЛС:</b> в боевом режиме цели появляются на дальности 27–39 км и могут залетать за пределы радара (36 км) ещё на ±4 км (до 40 км), временно выходя из зоны обнаружения РЛС.</li>
          <li><b>Каналы сопровождения и наведения (всего 5):</b> <b>3 канала РК</b>, <b>1 канал SACLOS</b> и <b>1 канал ОЭС</b>, из них <b>2 канала направленные</b> (SACLOS и ОЭС). При выходе цели из поля зрения ОЭС или срыве по доплеру в SACLOS наведение по направленному каналу срывается.</li>
          <li><b>ЗУР 95Я6:</b> боезапас 12 ракет, темп пуска 30 пусков/мин (интервал 2 с), дальность до 20 км, макс. скорость 1300 м/с, время управляемого полёта 30 с.</li>
          <li><b>Автопушки 2А38М:</b> боезапас 1404 снаряда (лента 351 снаряд), скорострельность 1250 выстр./мин, скорость снарядов ~960 м/с с автоматическим расчётом упреждения и баллистики. По умолчанию огонь заблокирован на дистанции &gt; 5 км (отключается во вкладке «Дополнительно»).</li>
        </ul>

        <h3 style="color:#ffd54f;">6. Нагрев, остывание и клин автопушек</h3>
        <ul>
          <li>Кнопка <b>ОГОНЬ 2А38М</b> работает по удержанию ЛКМ: пока держите — идёт очередь, отпустили — огонь прекращается.</li>
          <li><b>Тепловой баланс:</b> стартовая температура T₀ = 20 °C, нагрев +3.0 °C за выстрел, остывание в паузах по формуле ΔT<sub>охл</sub> = −0.08 · (T − 20) · Δt.</li>
          <li>От <b>350 °C</b> (~7 с непрерывного зажима) начинается зона риска теплового расширения и задержки; при достижении <b>680 °C</b> (~23–24 с непрерывного огня) происходит <b>необратимый клин стволов до перезапуска сценария</b>.</li>
        </ul>

        <h3 style="color:#ff8a80;">7. Контрманёвры, ответные пуски и поражение комплекса</h3>
        <ul>
          <li>При захвате или обстреле противники выполняют контрманёвры, включают активные помехи и применяют штатное подвесное вооружение (Х-31П, Х-59МК, AGM-88B HARM, AGM-65G, AASM Hammer-250 и др.) по позиции «Панциря».</li>
          <li>При засечении ответного пуска срабатывает звуковая тревога, в журнале появляется сообщение <b>КАПСОМ</b>, а кнопка быстрого перехвата позволяет сразу переключить приоритет на подлетающий боеприпас.</li>
          <li>В тепловизоре видны наши пуски ЗУР, трассеры автопушек в точку упреждения, взрыв и угасание сбитой цели, а также резкое расширение подлетающего вражеского боеприпаса перед ударом. При поражении комплекса отображаются помехи на весь экран, название поразившего боеприпаса и кнопка <b>«Вернуться к началу»</b> (сброс в не боевой режим с выключенной СУО).</li>
        </ul>

        <p style="color:#90a4ae;">Модель учебно-игровая: значения дальностей, порогов, баллистики и ЭПР условные и не отражают реальные характеристики комплекса.</p>
        """
        guide_view.setHtml(guide_html)
        layout.addWidget(guide_view, stretch=1)

        btn_row = QHBoxLayout()
        btn_row.addStretch(1)
        btn_to_std = QPushButton("<- К МОНИТОРУ 1 (ОЭС)")
        btn_to_std.clicked.connect(lambda: self.tabs.setCurrentIndex(0))
        btn_row.addWidget(btn_to_std)
        layout.addLayout(btn_row)

    def _apply_suo_power_state(self, powered: bool):
        try:
            self.suo_powered = bool(powered)
            if not hasattr(self, "btn_suo_power"):
                return
            self.btn_suo_power.blockSignals(True)
            self.btn_suo_power.setChecked(self.suo_powered)
            self.btn_suo_power.blockSignals(False)
            if hasattr(self, "plot_ascope"):
                self.plot_ascope.set_powered(self.suo_powered)
                self.plot_doppler.set_powered(self.suo_powered)

            if self.suo_powered:
                self.btn_suo_power.setText("СУО: ВКЛ")
                self.lbl_sys_ready.setText(" СИСТЕМА: ГОТОВА ")
                self.lbl_sys_ready.setStyleSheet("background-color: #76ff03; color: #000; font-weight: bold; padding: 2px 6px;")
                if hasattr(self, "thermal_widget"):
                    self.thermal_widget.powered = True
                    self.thermal_widget.update()
            else:
                self.gun_trigger_held = False
                self.btn_suo_power.setText("СУО: ВЫКЛ")
                self.lbl_sys_ready.setText(" СУО ОТКЛЮЧЕНА ")
                self.lbl_sys_ready.setStyleSheet("background-color: #ff5252; color: #fff; font-weight: bold; padding: 2px 6px;")
                self.lbl_top_telem.setText("СУО ОТКЛЮЧЕНА — ТЕПЛАК И РАДАР ОБЕСТОЧЕНЫ (ЦЕЛИ ПРОДОЛЖАЮТ ДВИЖЕНИЕ)")
                if hasattr(self, "lbl_oes_lock_badge"):
                    self.lbl_oes_lock_badge.setText(" СУО: ВЫКЛ ")
                    self.lbl_oes_lock_badge.setStyleSheet(
                        "background-color: #546e7a; color: #eceff1; font-weight: bold; padding: 4px;"
                    )
                if hasattr(self, "lbl_oes_card"):
                    self.lbl_oes_card.setText("СУО отключена")
                if hasattr(self, "oes_table"):
                    for r_i in range(self.oes_table.rowCount()):
                        it = self.oes_table.item(r_i, 1)
                        if it is not None:
                            it.setText("ВЫКЛ")
                if hasattr(self, "lbl_radar_card"):
                    self.lbl_radar_card.setText("<b>СУО ОТКЛЮЧЕНА</b><br>Питание РЛС и ОЭС снято. Цели движутся независимо.")
                if hasattr(self, "thermal_widget"):
                    self.thermal_widget.update_scene(None, 0.0, self.cam_az, self.cam_el, notch_masked=False, powered=False)
                if hasattr(self, "oes_sector_widget"):
                    self.oes_sector_widget.update_sector(self.cam_az, self.cam_el, None)
                if hasattr(self, "radar_widget"):
                    self.radar_widget.update_radar(
                        self.beam_az, [], -1, self.sector_mode, self.sector_center, self.sector_width, self.arc180_mode, self.beam_az, True
                    )
        except Exception as exc:
            _log_py_err("_apply_suo_power_state", exc)

    def _toggle_suo_power(self):
        try:
            new_state = bool(self.btn_suo_power.isChecked())
            self._apply_suo_power_state(new_state)
            if new_state:
                self._log_event("СУО включена: каналы ОЭС и РЛС запитаны", "INFO")
            else:
                self._log_event("СУО отключена: каналы ОЭС и РЛС обесточены", "WARN")
            QTimer.singleShot(0, self._tick)
        except Exception as exc:
            _log_py_err("_toggle_suo_power", exc)

    def _set_polarity(self, mode):
        self.thermal_widget.polarity = mode
        self.btn_whot.setChecked(mode == "WHOT")
        self.btn_bhot.setChecked(mode == "BHOT")
        self.btn_green.setChecked(mode == "GREEN")

    def _set_zoom(self, z):
        if self.thermal_widget.zoom_x != z:
            self.thermal_widget.zoom_x = z
            self.thermal_widget.trigger_zoom_glitch(0.2)
        self.btn_z1.setChecked(z == 1)
        self.btn_z2.setChecked(z == 2)
        self.btn_z4.setChecked(z == 4)

    def _toggle_auto_track(self):
        state = self.btn_auto_track.isChecked()
        self.thermal_widget.auto_track = state
        self.btn_auto_track.setText(f"АВТОСОПР: {'ВКЛ' if state else 'ВЫКЛ'}")

    def _on_manual_cam_change(self):
        self.cam_az = float(self.slider_cam_az.value())
        self.cam_el = float(self.slider_cam_el.value())
        self.lbl_manual_az.setText(f"АЗМ: {int(self.cam_az)}°")
        self.lbl_manual_el.setText(f"УМ: {int(self.cam_el)}°")

    def _sync_target_selection_from_oes(self, idx):
        self.combo_radar_target.blockSignals(True)
        self.combo_radar_target.setCurrentIndex(idx)
        self.combo_radar_target.blockSignals(False)

    def _sync_target_selection_from_radar(self, idx):
        self.combo_oes_target.blockSignals(True)
        self.combo_oes_target.setCurrentIndex(idx)
        self.combo_oes_target.blockSignals(False)

    def _toggle_run(self):
        self.is_running = not self.is_running

    def _toggle_sector_mode(self):
        self.sector_mode = self.btn_r_mode.isChecked()
        self.btn_r_mode.setText("РЕЖИМ: СЕКТОР 90°" if self.sector_mode else "РЕЖИМ: КРУГ 360°")

    def _cycle_freq(self):
        freqs = [2.5, 3.5, 10.0, 15.0]
        cur = freqs.index(self.f0_ghz) if self.f0_ghz in freqs else 0
        self.f0_ghz = freqs[(cur + 1) % len(freqs)]
        band = "S" if self.f0_ghz <= 4.0 else ("X" if self.f0_ghz <= 12.0 else "Ku")
        self.btn_r_freq.setText(f"ЧАСТОТА: {self.f0_ghz:.1f} ГГц ({band})")

    def _on_r_noise_change(self, val):
        self.noise_level = val / 100.0
        self.lbl_r_noise.setText(f"Помеховая обстановка: {val}%")
        if hasattr(self, "slider_x_noise"):
            self.slider_x_noise.blockSignals(True)
            self.slider_x_noise.setValue(val)
            self.slider_x_noise.blockSignals(False)
            self.lbl_x_noise.setText(f"Помеховая обстановка: {val}%")

    def _toggle_no_lock_scan(self):
        self.no_lock_scan = self.btn_no_lock_scan.isChecked()
        self.btn_no_lock_scan.setText(
            f"РЕЖИМ: СКАН БЕЗ ЗАХВАТА ({'ВКЛ' if self.no_lock_scan else 'ВЫКЛ'})"
        )

    def _toggle_arc180_mode(self):
        self.arc180_mode = self.btn_arc180_mode.isChecked()
        self.btn_arc180_mode.setText(
            f"ЗОНА 180° (ДОПЛЕР/ОБЗОР): {'ВКЛ' if self.arc180_mode else 'ВЫКЛ'}"
        )

    def _toggle_sector_follow(self):
        self.sector_follow_target = self.btn_sector_follow.isChecked()
        self.btn_sector_follow.setText(
            f"СЕКТОР 90° ЗА ЦЕЛЬЮ: {'ВКЛ' if self.sector_follow_target else 'ВЫКЛ'}"
        )

    def _on_sector_center_change(self, val):
        if self.sector_follow_target and not getattr(self, "_updating_sec_slider", False):
            self.sector_follow_target = False
            self.btn_sector_follow.setChecked(False)
            self.btn_sector_follow.setText("СЕКТОР 90° ЗА ЦЕЛЬЮ: ВЫКЛ")
        self.sector_center = float(val)
        self.lbl_r_sec.setText(f"Центр сектора обзора: {val}°")

    def _add_random_target(self):
        if len(self.targets) >= 16:
            return
        nid = self.next_target_id
        self.next_target_id += 1
        ang = np.random.uniform(0, 2 * math.pi)
        dist = np.random.uniform(26.0, 39.0) if self.combat_mode else np.random.uniform(8.0, 26.0)
        x = dist * math.sin(ang)
        y = dist * math.cos(ang)
        alt = np.random.uniform(1.5, 7.5)
        vx = np.random.uniform(-160, 160)
        vy = np.random.uniform(-160, 160)
        kind = np.random.choice(["fighter", "uav"])
        name = "Су-30СМ (Подкреп.)" if kind == "fighter" else "БПЛА-разведчик"
        rcs = 4.2 if kind == "fighter" else 0.65
        max_out = (MAX_RANGE_KM + COMBAT_EXTRA_OUT_KM) if self.combat_mode else (MAX_RANGE_KM * 0.94)
        t = SimTarget(nid, name, kind, x, y, alt, vx, vy, rcs=rcs, max_out_km=max_out)
        self.targets.append(t)
        self.combo_oes_target.addItem(f"Ц{t.id} — {t.name}")
        self.combo_radar_target.addItem(f"Ц{t.id} — {t.name}")

    def _trigger_beam_maneuver(self):
        sel_idx = self.combo_radar_target.currentIndex()
        if 0 <= sel_idx < len(self.targets):
            t = self.targets[sel_idx]
            spd = max(60.0, t.speed())
            _, az_deg, _ = t.polar()
            perp_deg = (az_deg + 90.0) % 360.0
            perp_rad = math.radians(perp_deg)
            t.vx = spd * math.sin(perp_rad)
            t.vy = spd * math.cos(perp_rad)

    def _format_sim_time(self):
        total = int(self.sim_time_sec)
        mm = (total // 60) % 60
        ss = total % 60
        return f"{mm:02d}:{ss:02d}"

    def _log_event(self, text, level="INFO"):
        ts = self._format_sim_time()
        color = "#ff8a80" if level == "WARN" else ("#ffd54f" if level == "PROG" else "#80cbc4")
        html_line = f'<span style="color:#78909c;">[{ts}]</span> <span style="color:{color};">{text}</span>'
        self.event_log_lines.append(html_line)
        if len(self.event_log_lines) > 140:
            self.event_log_lines = self.event_log_lines[-140:]
        if hasattr(self, "txt_event_log"):
            self.txt_event_log.setHtml("<br>".join(self.event_log_lines))
            sb = self.txt_event_log.verticalScrollBar()
            sb.setValue(sb.maximum())

    def _clear_event_log(self):
        self.event_log_lines.clear()
        if hasattr(self, "txt_event_log"):
            self.txt_event_log.clear()

    def _build_scenarios_tab(self, parent):
        layout = QHBoxLayout(parent)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(12)

        left_box = QFrame()
        left_box.setObjectName("PanelBlock")
        ll = QVBoxLayout(left_box)
        ll.setSpacing(6)

        hdr = QLabel("ВЫБОР ТАКТИЧЕСКОГО СЦЕНАРИЯ ОБСТАНОВКИ")
        hdr.setStyleSheet("background-color: #b0bec5; padding: 6px; font-weight: bold; font-size: 12.5px;")
        ll.addWidget(hdr)

        scenarios_info = [
            ("standard", "1. СТАНДАРТНАЯ ОБСТАНОВКА (СБРОС)", "Учебная обстановка: 3 истребителя и 1 БПЛА."),
            ("low_uav", "2. МАЛОВЫСОТНЫЙ БПЛА (МАЛАЯ ЭПР)", "Пара малоразмерных БПЛА на малой высоте в секторе 90°."),
            ("beam_evasion", "3. ТРАВЕРЗНЫЙ ПРОХОД (СРЫВ ДОПЛЕРА)", "Истребитель выходит на курс с Vr ≈ 0 в полосе режекции."),
            ("heavy_jam", "4. ПЛОТНЫЕ АКТИВНЫЕ ПОМЕХИ (78%)", "Высокий уровень помех (78%) с периодическими потерями отметок."),
            ("raid_group", "5. ГРУППОВОЙ НАЛЁТ (5 ЦЕЛЕЙ)", "Пять воздушных целей заходят в зоне 180°."),
            ("combat_intercept", "6. БОЕВОЙ РЕЖИМ (ЗАПУСК ПО СОСТАВУ СНИЗУ)", "Старт боевого режима с настроенным числом и составом противников, спавном вдали и залётом за радар на +4 км."),
        ]

        for sc_key, btn_title, desc in scenarios_info:
            card = QFrame()
            card.setStyleSheet("background-color: #eceff1; border: 1px solid #90a4ae; border-radius: 3px;")
            cl = QVBoxLayout(card)
            cl.setContentsMargins(8, 4, 8, 4)
            cl.setSpacing(2)

            btn = QPushButton(btn_title)
            btn.setMinimumHeight(26)
            if sc_key == "combat_intercept":
                btn.setStyleSheet("background-color: #ffcdd2; border: 2px solid #c62828; color: #b71c1c; font-weight: bold;")
            elif sc_key == "standard":
                btn.setStyleSheet("background-color: #c8e6c9; border: 1px solid #2e7d32; font-weight: bold;")
            btn.clicked.connect(lambda _chk=False, k=sc_key: self._apply_scenario(k))
            cl.addWidget(btn)

            lbl_d = QLabel(desc)
            lbl_d.setWordWrap(True)
            lbl_d.setStyleSheet("color: #263238; font-size: 10px;")
            cl.addWidget(lbl_d)
            ll.addWidget(card)

        # Настройка количества и состава противников для боевого режима
        cfg_card = QFrame()
        cfg_card.setStyleSheet("background-color: #fff8e1; border: 2px solid #f9a825; border-radius: 3px;")
        cfl = QVBoxLayout(cfg_card)
        cfl.setContentsMargins(8, 6, 8, 6)
        cfl.setSpacing(4)

        lbl_cfg_title = QLabel("НАСТРОЙКА ПРОТИВНИКОВ ДЛЯ БОЕВОГО РЕЖИМА:")
        lbl_cfg_title.setStyleSheet("font-weight: bold; color: #e65100;")
        cfl.addWidget(lbl_cfg_title)

        cnt_row = QHBoxLayout()
        cnt_row.addWidget(QLabel("Количество противников:"))
        self.spin_enemy_count = QSpinBox()
        self.spin_enemy_count.setRange(1, 10)
        self.spin_enemy_count.setValue(4)
        cnt_row.addWidget(self.spin_enemy_count)
        cnt_row.addStretch(1)
        cfl.addLayout(cnt_row)

        add_row = QHBoxLayout()
        self.combo_enemy_template = QComboBox()
        for t_name in ENEMY_TEMPLATES.keys():
            self.combo_enemy_template.addItem(t_name)
        add_row.addWidget(self.combo_enemy_template, stretch=1)

        btn_add_tpl = QPushButton("+ В СОСТАВ")
        btn_add_tpl.clicked.connect(self._add_enemy_to_roster)
        add_row.addWidget(btn_add_tpl)

        btn_rem_tpl = QPushButton("УДАЛИТЬ")
        btn_rem_tpl.clicked.connect(self._remove_enemy_from_roster)
        add_row.addWidget(btn_rem_tpl)
        cfl.addLayout(add_row)

        self.list_enemy_roster = QListWidget()
        self.list_enemy_roster.setMaximumHeight(78)
        for name_it in self.custom_combat_roster:
            self.list_enemy_roster.addItem(QListWidgetItem(name_it))
        cfl.addWidget(self.list_enemy_roster)

        ll.addWidget(cfg_card)
        layout.addWidget(left_box, stretch=3)

        right_box = QFrame()
        right_box.setObjectName("PanelBlock")
        rl = QVBoxLayout(right_box)
        rl.setSpacing(8)

        rhdr = QLabel("СТАТУС ТЕКУЩЕГО СЦЕНАРИЯ")
        rhdr.setStyleSheet("background-color: #b0bec5; padding: 6px; font-weight: bold; font-size: 12.5px;")
        rl.addWidget(rhdr)

        self.lbl_scenario_status = QLabel("—")
        self.lbl_scenario_status.setWordWrap(True)
        self.lbl_scenario_status.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.lbl_scenario_status.setStyleSheet(
            "background-color: #eceff1; border: 1px solid #90a4ae; padding: 10px; font-size: 12px;"
        )
        rl.addWidget(self.lbl_scenario_status, stretch=1)

        btn_restart_combat = QPushButton("↺ ПЕРЕЗАПУСТИТЬ БОЕВОЙ СЦЕНАРИЙ (СБРОС КЛИНА И БК)")
        btn_restart_combat.setMinimumHeight(34)
        btn_restart_combat.setStyleSheet("background-color: #ffe082; border: 1px solid #ef6c00; font-weight: bold;")
        btn_restart_combat.clicked.connect(lambda: self._apply_scenario("combat_intercept"))
        rl.addWidget(btn_restart_combat)

        btn_go_oes = QPushButton("ПЕРЕЙТИ НА МОНИТОР 1 (ОЭС / ОГОНЬ) ->")
        btn_go_oes.setMinimumHeight(32)
        btn_go_oes.clicked.connect(lambda: self.tabs.setCurrentIndex(0))
        rl.addWidget(btn_go_oes)

        layout.addWidget(right_box, stretch=2)
        self._refresh_scenario_status_card()

    def _add_enemy_to_roster(self):
        if not hasattr(self, "list_enemy_roster"):
            return
        if self.list_enemy_roster.count() >= 10:
            return
        name_txt = self.combo_enemy_template.currentText()
        self.list_enemy_roster.addItem(QListWidgetItem(name_txt))
        self.custom_combat_roster = [self.list_enemy_roster.item(i).text() for i in range(self.list_enemy_roster.count())]
        self.spin_enemy_count.setValue(self.list_enemy_roster.count())

    def _remove_enemy_from_roster(self):
        if not hasattr(self, "list_enemy_roster") or self.list_enemy_roster.count() <= 1:
            return
        row = self.list_enemy_roster.currentRow()
        if row < 0:
            row = self.list_enemy_roster.count() - 1
        self.list_enemy_roster.takeItem(row)
        self.custom_combat_roster = [self.list_enemy_roster.item(i).text() for i in range(self.list_enemy_roster.count())]
        self.spin_enemy_count.setValue(self.list_enemy_roster.count())

    def _refresh_scenario_status_card(self):
        if not hasattr(self, "lbl_scenario_status"):
            return
        lines_info = [
            f"<b>Активный сценарий:</b> {self.active_scenario_name}<br>",
            f"<b>Режим работы:</b> {'БОЕВОЙ' if self.combat_mode else 'УЧЕБНЫЙ'}",
            f"<b>Состояние 2А38М:</b> {'КЛИН СТВОЛОВ' if self.gun_jammed else f'ГОТОВА ({self.gun_temp:.0f}°C)'}",
            f"<b>Остаток БК:</b> ЗУР {self.sam_ammo}/12 | 30мм {self.gun_ammo}/1404<br>",
            "<b>Активные цели в воздухе:</b>",
        ]
        for t in self.targets:
            if not t.alive:
                continue
            r_s, az_s, _ = t.polar()
            ord_txt = f" | Подвес: {', '.join(t.ordnance)}" if t.ordnance else ""
            out_mark = " [ЗА РАДАРОМ >36КМ]" if r_s > MAX_RANGE_KM else ""
            lines_info.append(f"• Ц{t.id} {t.name}: Д={r_s:.1f} км{out_mark}, АЗМ={az_s:.0f}°{ord_txt}")
        self.lbl_scenario_status.setText("<br>".join(lines_info))

    def _rebuild_target_combos(self):
        self.combo_oes_target.blockSignals(True)
        self.combo_radar_target.blockSignals(True)
        self.combo_oes_target.clear()
        self.combo_radar_target.clear()
        for t in self.targets:
            self.combo_oes_target.addItem(f"Ц{t.id} — {t.name}")
            self.combo_radar_target.addItem(f"Ц{t.id} — {t.name}")
        if self.targets:
            self.combo_oes_target.setCurrentIndex(0)
            self.combo_radar_target.setCurrentIndex(0)
        self.combo_oes_target.blockSignals(False)
        self.combo_radar_target.blockSignals(False)

    def _apply_scenario(self, key):
        self.is_running = True
        self._prev_target_states.clear()
        self._reset_combat_systems()
        self.combat_mode = (key == "combat_intercept")
        if hasattr(self, "lbl_mode_badge"):
            if self.combat_mode:
                self.lbl_mode_badge.setText(" РЕЖИМ: БОЕВОЙ ")
                self.lbl_mode_badge.setStyleSheet("background-color: #ff5252; color: #fff; font-weight: bold; padding: 2px 6px;")
            else:
                self.lbl_mode_badge.setText(" РЕЖИМ: УЧЕБНЫЙ ")
                self.lbl_mode_badge.setStyleSheet("background-color: #b0bec5; color: #000; font-weight: bold; padding: 2px 6px;")

        if key == "standard":
            self.active_scenario_name = "Стандартная обстановка"
            self._init_targets()
            self.slider_r_noise.setValue(22)
            self.f0_ghz = 3.0
            self.sector_mode = False
            self.btn_r_mode.setChecked(False)
            self.btn_r_mode.setText("РЕЖИМ: КРУГ 360°")
            self.arc180_mode = False
            self.btn_arc180_mode.setChecked(False)
            self.btn_arc180_mode.setText("ЗОНА 180° (ДОПЛЕР/ОБЗОР): ВЫКЛ")
            self.no_lock_scan = False
            self.btn_no_lock_scan.setChecked(False)
            self.btn_no_lock_scan.setText("РЕЖИМ: СКАН БЕЗ ЗАХВАТА (ВЫКЛ)")

        elif key == "low_uav":
            self.active_scenario_name = "Маловысотный БПЛА (малая ЭПР)"
            self.targets = [
                SimTarget(1, "БПЛА-1 (Маловысотный)", "uav", 7.2, 11.5, 1.1, -28.0, -42.0, rcs=0.55),
                SimTarget(2, "БПЛА-2 (Разведчик)", "uav", 10.5, 9.0, 1.4, -34.0, -30.0, rcs=0.65),
                SimTarget(3, "Су-30СМ (Прикрытие)", "fighter", -16.0, 21.0, 6.2, 130.0, -145.0, rcs=4.8),
            ]
            self.next_target_id = 4
            self.slider_r_noise.setValue(28)
            self.sector_mode = True
            self.btn_r_mode.setChecked(True)
            self.btn_r_mode.setText("РЕЖИМ: СЕКТОР 90°")

        elif key == "beam_evasion":
            self.active_scenario_name = "Траверзный проход (срыв доплера)"
            self.targets = [
                SimTarget(1, "F-16C (Такт. истреб.)", "fighter", 14.0, 14.0, 5.2, 155.0, -152.0, rcs=3.4),
                SimTarget(2, "Су-30СМ (Истребитель)", "fighter", -12.0, 20.0, 6.8, 120.0, -170.0, rcs=5.0),
            ]
            self.next_target_id = 3
            self.slider_r_noise.setValue(20)

        elif key == "heavy_jam":
            self.active_scenario_name = "Плотные активные помехи (78%)"
            self.targets = [
                SimTarget(1, "Rafale (Постановщик помех)", "fighter", 15.0, 17.0, 6.4, -145.0, -135.0, rcs=3.8),
                SimTarget(2, "F-16C (Ударный)", "fighter", -19.0, 18.0, 5.0, 155.0, -120.0, rcs=3.2),
                SimTarget(3, "Су-30СМ (Истребитель)", "fighter", 9.0, 13.5, 5.8, -110.0, -155.0, rcs=5.0),
                SimTarget(4, "Boeing 747 (Крупный лайнер)", "liner", -26.0, -12.0, 10.2, 170.0, 150.0, rcs=18.0),
            ]
            self.next_target_id = 5
            self.slider_r_noise.setValue(78)

        elif key == "raid_group":
            self.active_scenario_name = "Групповой налёт (5 целей)"
            self.targets = [
                SimTarget(1, "Су-30СМ (Ведущий)", "fighter", 11.0, 23.0, 6.8, -135.0, -185.0, rcs=5.0),
                SimTarget(2, "Су-30СМ (Ведомый)", "fighter", 15.5, 21.0, 6.5, -140.0, -180.0, rcs=4.8),
                SimTarget(3, "F-16C (Фланговый)", "fighter", -16.0, 19.0, 4.9, 165.0, -145.0, rcs=3.3),
                SimTarget(4, "БПЛА-1 (Разведка)", "uav", 4.5, 14.0, 1.8, -18.0, -48.0, rcs=0.65),
                SimTarget(5, "БПЛА-2 (Ударный)", "uav", -6.0, 12.5, 1.5, 25.0, -44.0, rcs=0.60),
            ]
            self.next_target_id = 6
            self.slider_r_noise.setValue(30)
            self.arc180_mode = True
            self.btn_arc180_mode.setChecked(True)
            self.btn_arc180_mode.setText("ЗОНА 180° (ДОПЛЕР/ОБЗОР): ВКЛ")

        elif key == "combat_intercept":
            self.active_scenario_name = "БОЕВОЙ РЕЖИМ (ОТВЕТНЫЙ ОГОНЬ И ПЕРЕХВАТ)"
            if hasattr(self, "list_enemy_roster") and self.list_enemy_roster.count() > 0:
                self.custom_combat_roster = [self.list_enemy_roster.item(i).text() for i in range(self.list_enemy_roster.count())]
            desired_cnt = self.spin_enemy_count.value() if hasattr(self, "spin_enemy_count") else len(self.custom_combat_roster)
            self.targets = self._build_combat_targets_from_roster(self.custom_combat_roster, desired_cnt)
            self.slider_r_noise.setValue(20)
            self.sector_mode = False
            self.btn_r_mode.setChecked(False)
            self.btn_r_mode.setText("РЕЖИМ: КРУГ 360°")
            self.arc180_mode = False
            self.btn_arc180_mode.setChecked(False)
            self.btn_arc180_mode.setText("ЗОНА 180° (ДОПЛЕР/ОБЗОР): ВЫКЛ")
            self.no_lock_scan = False
            self.btn_no_lock_scan.setChecked(False)
            self.btn_no_lock_scan.setText("РЕЖИМ: СКАН БЕЗ ЗАХВАТА (ВЫКЛ)")
            if not self.suo_powered:
                self._apply_suo_power_state(True)

        self._rebuild_target_combos()
        if self.targets:
            _, az0, el0 = self.targets[0].polar()
            self.sector_center = az0
            self.cam_az = az0
            self.cam_el = el0
        self._refresh_scenario_status_card()
        self._log_event(f"Загружен сценарий: «{self.active_scenario_name}» (целей: {len(self.targets)})", "WARN" if self.combat_mode else "INFO")

    def _reset_sim(self):
        self._apply_scenario("combat_intercept" if self.combat_mode else "standard")

    def _update_combat_hud(self):
        if not hasattr(self, "lbl_ammo_status"):
            return
        belt_rem = self.gun_ammo % GUN_BELT_SIZE
        if belt_rem == 0 and self.gun_ammo > 0:
            belt_rem = GUN_BELT_SIZE
        self.lbl_ammo_status.setText(f"БК 2А38М: {self.gun_ammo} (лента {belt_rem}) | ЗУР 95Я6: {self.sam_ammo}")

        self.bar_gun_temp.setValue(int(min(TEMP_CRIT, max(TEMP_AMBIENT, self.gun_temp))))
        if self.gun_jammed:
            self.lbl_gun_temp.setText(f"T СТВОЛОВ: {self.gun_temp:.0f}°C [КЛИН! ПЕРЕЗАПУСК]")
            self.lbl_gun_temp.setStyleSheet("font-size: 10.5px; font-weight: bold; color: #d50000;")
        elif self.gun_temp >= TEMP_WARN:
            self.lbl_gun_temp.setText(f"T СТВОЛОВ: {self.gun_temp:.0f}°C [ПЕРЕГРЕВ / РИСК]")
            self.lbl_gun_temp.setStyleSheet("font-size: 10.5px; font-weight: bold; color: #ef6c00;")
        else:
            self.lbl_gun_temp.setText(f"T СТВОЛОВ: {self.gun_temp:.0f}°C [НОРМА]")
            self.lbl_gun_temp.setStyleSheet("font-size: 10.5px; font-weight: bold; color: #1b5e20;")

        rk_cnt, saclos_cnt, oes_cnt, dir_cnt = self._get_channel_counts()
        ch_str = f"КАНАЛЫ: РК {rk_cnt}/3 | SACLOS {saclos_cnt}/1 | ОЭС {oes_cnt}/1 (НАПР: {dir_cnt}/2)"
        self.lbl_channels_detail.setText(ch_str)
        self.lbl_chan_info.setText(f" {ch_str} | {self.f0_ghz:.1f} ГГц ")

        t = self._get_selected_target()
        dist_blocked = False
        if t is not None and t.alive and self.gun_range_limit_enabled:
            r_km, _, _ = t.polar()
            if r_km > GUN_DEFAULT_RANGE_LIMIT_KM:
                dist_blocked = True

        can_gun = (
            self.suo_powered and self.combat_mode and (not self.gun_jammed)
            and (self.gun_ammo > 0) and (t is not None) and t.alive
            and (not self.no_lock_scan) and (not dist_blocked)
        )
        self.btn_fire_gun.setEnabled(can_gun)
        if self.gun_jammed:
            self.btn_fire_gun.setText("2А38М: КЛИН\n(НУЖЕН СБРОС)")
        elif dist_blocked:
            self.btn_fire_gun.setText("ОГОНЬ 2А38М\n(ДАЛЬНОСТЬ > 5КМ)")
        else:
            self.btn_fire_gun.setText("ОГОНЬ 2А38М\n(УДЕРЖ. ЛКМ)")

        can_sam = (
            self.suo_powered and self.combat_mode and (self.sam_ammo > 0)
            and (self.sam_cooldown <= 0.0) and (t is not None) and t.alive and (not self.no_lock_scan)
        )
        self.btn_launch_sam.setEnabled(can_sam)

    def _tick(self):
        try:
            self._tick_inner()
        except Exception as exc:
            _log_py_err("_tick_inner", exc)
        try:
            if self.tabs.currentWidget() is self.tab_extra:
                self._update_extra_tab()
            elif hasattr(self, "tab_scenarios") and self.tabs.currentWidget() is self.tab_scenarios:
                self._refresh_scenario_status_card()
        except Exception as exc:
            _log_py_err("_tick_tabs", exc)

    def _tick_inner(self):
        dt_real = 0.045
        if self.sam_cooldown > 0.0:
            self.sam_cooldown = max(0.0, self.sam_cooldown - dt_real)

        self._process_gun_firing_step(dt_real)

        if not getattr(self, "suo_powered", False):
            if self.is_running:
                self.sim_time_sec += dt_real
                for t in self.targets:
                    t.step(0.20)
            self._apply_suo_power_state(False)
            self._update_combat_hud()
            return

        if self.is_running:
            self.sim_time_sec += dt_real
        self.thermal_widget.tick_glitch(dt_real)

        for tr in self.active_tracers:
            if not tr.active:
                continue
            tr.elapsed += dt_real
            if tr.elapsed >= tr.travel_time_total:
                tr.active = False
                if tr.hit_will_occur:
                    t_sel = self._get_selected_target()
                    if t_sel is not None and t_sel.alive:
                        t_sel.hp -= 28.0
                        if t_sel.hp <= 0.0:
                            t_sel.kill_with_explosion()
                            self._release_channel_if_unused(t_sel.id)
                            self._log_event(f"ЦЕЛЬ Ц{t_sel.id} ({t_sel.name}) СБИТА ОГНЁМ АВТОПУШЕК 2А38М!", "INFO")
        self.active_tracers = [tr for tr in self.active_tracers if tr.active]

        target_by_id = {t.id: t for t in self.targets}
        for sam in self.active_sams:
            if not sam.active:
                continue
            sam.flight_time += dt_real
            tgt = target_by_id.get(sam.target_id)
            if tgt is None or not tgt.alive:
                sam.active = False
                self._release_channel_if_unused(sam.target_id)
                continue
            if sam.flight_time > SAM_FLIGHT_TIME_SEC:
                sam.active = False
                self._release_channel_if_unused(sam.target_id)
                self._log_event(f"ЗУР 95Я6 #{sam.id}: самоликвидация по истечении 30 с полёта", "WARN")
                continue

            if sam.is_directed:
                _, t_az_now, _t_el_now = tgt.polar()
                if sam.channel_mode == "ОЭС":
                    if abs(ang_diff_deg(t_az_now, self.cam_az)) > (self.thermal_widget.fov_deg * 0.65):
                        sam.active = False
                        self._release_channel_if_unused(sam.target_id)
                        self._log_event(f"ЗУР 95Я6 #{sam.id}: СРЫВ НАПРАВЛЕННОГО КАНАЛА ОЭС (ЦЕЛЬ УШЛА ИЗ КАДРА)", "WARN")
                        continue
                elif sam.channel_mode == "SACLOS":
                    if tgt.clutter_notched:
                        sam.active = False
                        self._release_channel_if_unused(sam.target_id)
                        self._log_event(f"ЗУР 95Я6 #{sam.id}: СРЫВ НАПРАВЛЕННОГО КАНАЛА SACLOS (МАНЁВР ЦЕЛИ)", "WARN")
                        continue

            dx = tgt.x - sam.x
            dy = tgt.y - sam.y
            dz = tgt.alt - sam.alt
            dist_km = math.sqrt(dx * dx + dy * dy + dz * dz)
            step_km = (SAM_SPEED_MS / 1000.0) * dt_real * 2.2
            if dist_km <= max(0.28, step_km):
                sam.active = False
                tgt.kill_with_explosion()
                self._release_channel_if_unused(sam.target_id)
                self._log_event(f"ПРЯМОЕ ПОПАДАНИЕ ЗУР 95Я6 #{sam.id}! ЦЕЛЬ Ц{tgt.id} ({tgt.name}) УНИЧТОЖЕНА!", "INFO")
            else:
                sam.x += (dx / dist_km) * step_km
                sam.y += (dy / dist_km) * step_km
                sam.alt += (dz / dist_km) * step_km
                r_h = math.hypot(sam.x, sam.y)
                sam.az = math.degrees(math.atan2(sam.x, sam.y)) % 360.0
                sam.el = math.degrees(math.atan2(sam.alt, max(0.05, r_h)))
        self.active_sams = [s for s in self.active_sams if s.active]

        half_sec = self.sector_width * 0.5
        half_180 = self.radar_widget.arc180_width * 0.5
        prev_beam = self.beam_az
        if not hasattr(self, "dashed_az"):
            self.dashed_az = self.beam_az
        if not hasattr(self, "dashed_dir"):
            self.dashed_dir = 1
        prev_dashed = self.beam_az if self.no_lock_scan else self.dashed_az

        sel_idx_tick = self.combo_radar_target.currentIndex()
        cand_t = self.targets[sel_idx_tick] if 0 <= sel_idx_tick < len(self.targets) else None
        has_active_lock = False
        locked_target_az = None
        if (not self.no_lock_scan) and cand_t is not None and cand_t.alive:
            c_r, c_az, _ = cand_t.polar()
            c_vr = cand_t.radial_vel()
            c_snr = (cand_t.rcs * 11.5) / max(1.5, c_r)
            eff_noise_c = min(1.0, self.noise_level + cand_t.jamming_boost)
            c_noise_thresh = detection_threshold(eff_noise_c)
            c_in90 = (not self.sector_mode) or (abs(ang_diff_deg(c_az, self.sector_center)) <= half_sec)
            c_in180 = (not self.arc180_mode) or (abs(ang_diff_deg(c_az, self.sector_center)) <= half_180)
            if (c_r <= MAX_RANGE_KM) and (c_snr > c_noise_thresh) and c_in90 and c_in180 and (abs(c_vr) >= NOTCH_VR_MS):
                has_active_lock = True
                locked_target_az = c_az

        if self.is_running:
            dt = 0.20
            if has_active_lock and locked_target_az is not None:
                self.beam_az = locked_target_az % 360.0
            elif self.sector_mode or self.arc180_mode:
                scan_half = half_sec if self.sector_mode else half_180
                self.beam_az = (self.beam_az + self.sector_dir * 4.5) % 360.0
                diff = ang_diff_deg(self.beam_az, self.sector_center)
                if diff > scan_half:
                    self.sector_dir = -1
                    self.beam_az = (self.sector_center + scan_half) % 360.0
                elif diff < -scan_half:
                    self.sector_dir = 1
                    self.beam_az = (self.sector_center - scan_half) % 360.0
            else:
                self.beam_az = (self.beam_az + 5.5) % 360.0

            if self.no_lock_scan:
                self.dashed_az = self.beam_az
            elif self.sector_mode or self.arc180_mode:
                scan_half = half_sec if self.sector_mode else half_180
                self.dashed_az = (self.dashed_az + self.dashed_dir * 4.5) % 360.0
                d_sec = ang_diff_deg(self.dashed_az, self.sector_center)
                if d_sec > scan_half:
                    self.dashed_dir = -1
                    self.dashed_az = (self.sector_center + scan_half) % 360.0
                elif d_sec < -scan_half:
                    self.dashed_dir = 1
                    self.dashed_az = (self.sector_center - scan_half) % 360.0
            else:
                self.dashed_az = (self.dashed_az + 5.5) % 360.0

            curr_dashed = self.dashed_az

            for idx, t in enumerate(list(self.targets)):
                t.step(dt)
                if not t.alive:
                    continue

                if self.combat_mode and (not t.is_munitions) and t.ordnance:
                    t.attack_cooldown -= dt_real
                    r_now, _, _ = t.polar()
                    if t.attack_cooldown <= 0.0 and r_now <= 24.0:
                        t.attack_cooldown = random.uniform(11.0, 17.0)
                        self._spawn_enemy_ordnance(t)

                if t.is_munitions and t.alive:
                    r_m, _, _ = t.polar()
                    if r_m <= 0.25:
                        t.alive = False
                        self.gun_trigger_held = False
                        self.sound_engine.play_alarm(self.sim_time_sec + 1.0)
                        self._log_event(f"КРИТИЧЕСКОЕ ПОРАЖЕНИЕ КОМПЛЕКСА БОЕПРИПАСОМ: {t.name.upper()}!", "WARN")
                        self.destroyed_overlay.show_destroyed(t.name)
                        return

                r_slant, az, _ = t.polar()
                vr = t.radial_vel()
                snr = (t.rcs * 11.5) / max(1.5, r_slant)
                eff_noise_t = min(1.0, self.noise_level + t.jamming_boost)
                noise_thresh = detection_threshold(eff_noise_t)
                in_radar_range = (r_slant <= MAX_RANGE_KM)
                in_90 = (not self.sector_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_sec)
                in_180 = (not self.arc180_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_180)
                t.in_sector = in_radar_range and in_90 and in_180
                t.clutter_notched = (not t.is_munitions) and (abs(vr) < NOTCH_VR_MS)
                t.detected = (snr > noise_thresh) and t.in_sector

                live_ok = bool(t.detected and not t.clutter_notched)
                t.update_track_coasting(live_ok, dt, dt_real)

                prev_st = self._prev_target_states.get(t.id)
                if prev_st is not None:
                    prev_live, prev_vis = prev_st
                    if prev_live and not live_ok:
                        if not in_radar_range:
                            reason = "выход за пределы радара (>36 км)"
                        elif not in_90:
                            reason = "выход из сектора обзора 90°"
                        elif not in_180:
                            reason = "выход из зоны 180°"
                        elif t.clutter_notched:
                            reason = "нулевая радиальная скорость (режекция)"
                        else:
                            reason = "помехи / сигнал ниже порога"
                        self._log_event(f"Ц{t.id}: срыв сопровождения ({reason}), прогноз 4.0с", "WARN")
                    elif (not prev_live) and live_ok:
                        self._log_event(f"Ц{t.id}: отметка восстановлена (Д={r_slant:.1f} км, АЗМ={az:.0f}°)", "INFO")
                    elif prev_vis and (not t.track_visible):
                        self._log_event(f"Ц{t.id}: прогноз завершён, отметка снята с индикатора", "PROG")
                self._prev_target_states[t.id] = (live_ok, t.track_visible)

                is_locked_t = (not self.no_lock_scan) and (idx == sel_idx_tick) and live_ok
                if live_ok:
                    if is_locked_t or t.is_munitions:
                        t.refresh_from_radar(self.f0_ghz)
                    else:
                        t.step_radar_extrapolation(dt, dt_real)
                        dashed_zone_ok = (not self.no_lock_scan) and in_90 and in_radar_range
                        hit_solid = (in_90 and in_radar_range) and beam_crossed_az(prev_beam, self.beam_az, az, margin_deg=3.0)
                        hit_dashed = dashed_zone_ok and beam_crossed_az(prev_dashed, curr_dashed, az, margin_deg=3.0)
                        if hit_solid or hit_dashed:
                            t.refresh_from_radar(self.f0_ghz)
                else:
                    t.radar_update_flash = 0.0
        else:
            curr_dashed = self.dashed_az

        sel_idx = self.combo_radar_target.currentIndex()
        sel_t = self.targets[sel_idx] if 0 <= sel_idx < len(self.targets) else None
        ch_map_simple = {tid: info["mode"] for tid, info in self.channel_assignments.items()}

        if self.no_lock_scan:
            self.lbl_top_telem.setText("РЕЖИМ: БЕЗ ЗАХВАТА — СВОБОДНОЕ СКАНИРОВАНИЕ МЕСТНОСТИ")
            self.lbl_oes_lock_badge.setText(" ЗАХВАТ: СНЯТ (СКАН) ")
            self.lbl_oes_lock_badge.setStyleSheet(
                "background-color: #ffd54f; color: #000; font-weight: bold; padding: 4px;"
            )
            self.lbl_oes_card.setText("Режим свободного сканирования: цель не захвачена")
            for r_i in range(self.oes_table.rowCount()):
                self.oes_table.item(r_i, 1).setText("СКАН" if r_i == 4 else "—")
            self.thermal_widget.update_scene(
                None, self.noise_level, self.cam_az, self.cam_el, notch_masked=False, powered=self.suo_powered,
                active_sams=self.active_sams, active_tracers=self.active_tracers, all_targets=self.targets
            )
            self.oes_sector_widget.update_sector(self.cam_az, self.cam_el, None)
            self.radar_widget.update_radar(
                self.beam_az, self.targets, -1, self.sector_mode, self.sector_center, self.sector_width,
                self.arc180_mode, curr_dashed, True, self.active_sams, ch_map_simple
            )
            self._update_combat_hud()
            return

        if sel_t is not None:
            r_slant, az, el = sel_t.polar()
            vr = sel_t.radial_vel()
            fd = sel_t.doppler_khz(self.f0_ghz)
            in_range_now = (r_slant <= MAX_RANGE_KM)
            in_90_now = (not self.sector_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_sec)
            in_180_now = (not self.arc180_mode) or (abs(ang_diff_deg(az, self.sector_center)) <= half_180)
            in_sec_now = in_range_now and in_90_now and in_180_now
            notched_now = (not sel_t.is_munitions) and (abs(vr) < NOTCH_VR_MS)
            live_ok_now = bool(sel_t.alive and sel_t.detected and not notched_now)

            if not sel_t.alive:
                st_txt = "ЦЕЛЬ ПОРАЖЕНА"
                coord_line = "Дальность / Высота: <b>ПОРАЖЕНА</b><br>Азимут / Курс: <b>—</b>"
                top_coord = "ЦЕЛЬ ПОРАЖЕНА"
                lock_ok = False
            elif sel_t.is_coasting:
                rem = max(0.0, COAST_DURATION_SEC - sel_t.coast_elapsed)
                phase_txt = f"ПРОГНОЗ {rem:.1f}с" if sel_t.coast_elapsed < COAST_DURATION_SEC else "УГАСАНИЕ"
                st_txt = f"СРЫВ СОПРОВОЖДЕНИЯ — {phase_txt}"
                coord_line = f"Дальность / Высота: <b>ПРОГНОЗ / ПОТЕРЯНО</b><br>Азимут / Курс: <b>{phase_txt}</b>"
                top_coord = f"ЦЕЛЬ ПОТЕРЯНА ({phase_txt})"
                lock_ok = False
            elif not in_sec_now:
                if not in_range_now:
                    st_txt = f"ЗА ПРЕДЕЛАМИ РАДАРА (Д={r_slant:.1f} км > 36 км)"
                elif self.arc180_mode and not in_180_now:
                    st_txt = "ВНЕ ЗОНЫ 180°"
                else:
                    st_txt = "ВНЕ СЕКТОРА ОБЗОРА 90°"
                coord_line = f"Дальность / Высота: <b>{st_txt}</b><br>Азимут / Курс: <b>{st_txt}</b>"
                top_coord = st_txt
                lock_ok = False
            elif not sel_t.detected:
                st_txt = "СРЫВ СОПРОВОЖДЕНИЯ / КООРДИНАТЫ ПОТЕРЯНЫ"
                coord_line = "Дальность / Высота: <b>КООРДИНАТЫ ПОТЕРЯНЫ</b><br>Азимут / Курс: <b>КООРДИНАТЫ ПОТЕРЯНЫ</b>"
                top_coord = "КООРДИНАТЫ ПОТЕРЯНЫ"
                lock_ok = False
            elif notched_now:
                st_txt = "ЗАХВАТ СБИТ (ПОТЕРЯ ДОПЛЕРОВСКОГО СИГНАЛА: Vr≈0)"
                coord_line = (
                    f"Дальность / Высота: {r_slant:.2f} км / {sel_t.alt:.1f} км<br>"
                    f"Азимут / Курс: {az:.1f}° / {sel_t.heading_deg():.0f}°"
                )
                top_coord = f"Д={r_slant:.1f} км | ЗАХВАТ СБИТ (Vr={vr:+.0f} м/с)"
                lock_ok = False
            else:
                st_txt = "ПОСТОЯННОЕ СЛЕЖЕНИЕ (ЗАХВАТ)"
                coord_line = (
                    f"Дальность / Высота: {r_slant:.2f} км / {sel_t.alt:.1f} км<br>"
                    f"Азимут / Курс: {az:.1f}° / {sel_t.heading_deg():.0f}°"
                )
                top_coord = f"Д={r_slant:.1f} км | АЗМ={az:.1f}° | УМ={el:.1f}°"
                if self.sector_follow_target:
                    self.sector_center = az
                    self._updating_sec_slider = True
                    self.slider_r_sec.setValue(int(round(az)) % 360)
                    self._updating_sec_slider = False
                    self.lbl_r_sec.setText(f"Центр сектора обзора: {int(round(az)) % 360}° (за целью)")
                if self.thermal_widget.auto_track:
                    self.cam_az = az
                    self.cam_el = el
                lock_ok = self.thermal_widget.zoom_glitch_sec <= 0.0

            self.lbl_top_telem.setText(f"ЦЕЛЬ №{sel_t.id} ({sel_t.name}) | {top_coord}")

            if lock_ok:
                self.lbl_oes_lock_badge.setText(" ЗАХВАТ: УДЕРЖАН ")
                self.lbl_oes_lock_badge.setStyleSheet(
                    "background-color: #76ff03; color: #000; font-weight: bold; padding: 4px;"
                )
                lock_cell = "ЗАХВАТ"
            else:
                badge_txt = " ЦЕЛЬ ПОРАЖЕНА " if not sel_t.alive else (
                    " ЗАХВАТ: СБИТ (Vr≈0) " if (notched_now and in_sec_now and sel_t.detected) else " ЗАХВАТ: СБИТ "
                )
                self.lbl_oes_lock_badge.setText(badge_txt)
                self.lbl_oes_lock_badge.setStyleSheet(
                    "background-color: #ff5252; color: #fff; font-weight: bold; padding: 4px;"
                )
                lock_cell = "ПОРАЖЕНА" if not sel_t.alive else ("СБИТ (Vr≈0)" if (notched_now and in_sec_now and sel_t.detected) else "СБИТ")

            self.lbl_oes_card.setText(
                f"Ц{sel_t.id}: {sel_t.name} | {'АВТО' if self.thermal_widget.auto_track else 'РУЧН.'}"
            )

            vals_col = [
                f"{r_slant:.1f} км" if live_ok_now else ("ПРОГНОЗ" if sel_t.is_coasting else "ПОТЕРЯНА"),
                f"{az:.1f}°" if live_ok_now else "—",
                f"{el:.1f}°" if live_ok_now else "—",
                f"{int(sel_t.speed())} м/с (Vr={vr:+.0f})" if sel_t.alive else "—",
                lock_cell,
                f"x{self.thermal_widget.zoom_x} / {int(round(self.noise_level * 100))}%",
            ]
            for r_i, v_str in enumerate(vals_col):
                self.oes_table.item(r_i, 1).setText(v_str)

            ord_info = f"<br>Подвес: {', '.join(sel_t.ordnance)}" if sel_t.ordnance else ""
            self.lbl_radar_card.setText(
                f"<b>ФОРМУЛЯР ЦЕЛИ №{sel_t.id}:</b><br>"
                f"Тип: {sel_t.name}{ord_info}<br>"
                f"{coord_line}<br>"
                f"Скорость путевая / рад.: {sel_t.speed():.0f} м/с / {vr:+.0f} м/с<br>"
                f"Доплеровский сдвиг: {fd:+.2f} кГц<br>"
                f"Статус РЛС: <b>{st_txt}</b>"
            )

        self.thermal_widget.update_scene(
            sel_t,
            self.noise_level,
            self.cam_az,
            self.cam_el,
            notch_masked=(sel_t is not None and sel_t.alive and (not sel_t.is_munitions) and abs(sel_t.radial_vel()) < NOTCH_VR_MS),
            powered=self.suo_powered,
            active_sams=self.active_sams,
            active_tracers=self.active_tracers,
            all_targets=self.targets,
        )
        self.oes_sector_widget.update_sector(self.cam_az, self.cam_el, sel_t)
        self.radar_widget.update_radar(
            self.beam_az, self.targets, sel_idx, self.sector_mode, self.sector_center, self.sector_width,
            self.arc180_mode, curr_dashed, False, self.active_sams, ch_map_simple
        )
        self._update_combat_hud()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    win = PantsirCombatWorkstation()
    win.show()
    sys.exit(app.exec())
