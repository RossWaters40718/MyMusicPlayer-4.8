import tkinter as tk
from tkinter import *
from tkinter import ttk, font, filedialog, messagebox
import numpy as np
from pathlib import Path
from win32api import GetMonitorInfo, MonitorFromPoint
import eyed3
from eyed3.id3.frames import ImageFrame
import mutagen
from PIL import Image, ImageTk
import glob
from winsdk.windows.devices import radios
import pygame
import pygame._sdl2.audio as sdl2_audio
from pygame.locals import * # Event Keys
import pyaudio
from ctypes import cast, POINTER
from comtypes import CLSCTX_ALL
from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
import asyncio
import subprocess
import psutil
import json
import random
from ffmpy import FFmpeg, FFRuntimeError
import concurrent.futures
import time
import os
import sys
class Audio_Converter():
    def __init__(self):
        self.Extension_Options={
                "aac":{"codec":"aac","codec":"aac","options":{"low":"-b:a 64k","medium":"-b:a 128k","high":"-b:a 256k",},},
                "aiff":{"codec":"pcm_s16be","options":{"low":"","medium":"","high":"",},},
                "alac":{"codec":"alac","options":{"low":"","medium":"","high":"",},},
                "ape":{"codec":"ape","options":{"low":"","medium":"","high":"",},},
                "flac":{"codec":"flac","options":{"low":"-compression_level 1","medium":"-compression_level 5","high":"-compression_level 8",},},
                "mp3":{"codec": "libmp3lame","options": {"low":"-q 5","medium":"-q 2","high":"-b:a 320k",},},
                "m4a":{"codec":"aac","options":{"low":"-b:a 64k","medium":"-b:a 128k","high":"-b:a 256k",},},
                "ogg":{"codec":"libvorbis","options":{"low":"-qscale:a 3","medium":"-qscale:a 5","high":"-qscale:a 7",},},
                "opus":{"codec":"libopus","options":{"low":"-b:a 64k","medium":"-b:a 128k","high":"-b:a 192k",},},
                "wma":{"codec":"wmav2","options":{"low":"-b:a 64k","medium":"-b:a 128k","high":"-b:a 192k",},},}
    def convert_audio(self,input_file, output_format, input_format, audio_quality, overwrite, preserve_metadata):
        output_file=input_file[:-len(input_format)] + f'{output_format}'
        if os.path.exists(output_file) and not overwrite:
            return (False, (input_file, output_file))
        codec=self.Extension_Options[output_format]["codec"]
        ffmpeg_options=f'-loglevel panic -y {self.Extension_Options[output_format]["options"][audio_quality]} -acodec {codec}'
        if preserve_metadata:
            ffmpeg_options+=' -map_metadata 0'
        try:
            fpg=FFmpeg(executable=ffmpeg_path,inputs={input_file: None},outputs={output_file:ffmpeg_options})
            fpg.run()
        except FFRuntimeError as e:
            return (False, f"{input_file}: {str(e)}")
        return (True, (input_file, output_file))
    def convert_start(self,folder_path, input_format,output_format,one_file=None):
        audio_quality='high'
        overwrite='store_true'
        preserve_metadata=False
        audio_files=[]
        formats_supported=[fmt for fmt in list(self.Extension_Options.keys()) if fmt!=output_format]
        if one_file==None:
            for root, _, files in os.walk(folder_path):# Retrieve Audio Files With Selected Extension
                for file in files:
                    file_ext=file.lower().split('.')[-1]
                    if file_ext==input_format and input_format in formats_supported:
                        file_path=os.path.join(root, file)
                        audio_files.append(file_path)
        else:
            file_name=os.path.basename(folder_path)
            file_ext=os.path.splitext(file_name)[1].replace(".","")
            if file_ext==input_format and input_format in formats_supported:
                audio_files.append(folder_path)
        if not audio_files:return
        with concurrent.futures.ThreadPoolExecutor() as executor:
            futures=[executor.submit(self.convert_audio, audio_file, output_format, input_format, 
                                     audio_quality, overwrite, preserve_metadata) for audio_file in audio_files]
            results={}
            for i,future in enumerate(concurrent.futures.as_completed(futures)):
                arg = futures[i]
                results[arg] = future.result()
        futures.clear()    
        executor.shutdown(wait=True)
        msg3=""    
        for i,file in enumerate(audio_files):
            key=list(results.keys())[i]
            value=results.get(key)
            msg3+=str("Music File:" +str(value[1]))+"\n"
            msg3+=str("Conversion Passed:" +str(value[0]))+"\n"
        msg1="Music Conversions Completed!\n"       
        msg2="Music Files Converted to MP3:\n"
        msg=msg1+msg2+msg3
        messagebox.showinfo("<Music Conversions Completed>", msg)
        return results
class Audio_Player():
    def __init__(self, parent):
        self.parent=parent
        self.Active_Device=""# Selected Playback Device
        self.Master_Volume=None
        self.Check_List=[]# Duplicate Check
        self.Results={}# Song Dictionary
        self.Songs={}# Shuffled Songs
        self.index_info=()    
        self.Index=[]
        self.Music=[]# Song Widgets
        self.Music_Count=0# Song Widget Count
        self.Visualizer=[]
        self.Vis_Counter=0
        self.Vis_Widgets=0
        self.Vis_Time=0.00# Music Notes Visualization
        self.vis_info=()
        self.key_now=None# Active Song Key
        self.last_key=None
        self.repeat=False
        self.song_selected=""
        self.active_Song=""
        self.song=""
        self.song_info=()
        self.time_delta=0.00# Manual Change In Slider Position
        self.paused=False
        self.art=None
        self.art_size=()
        self.artsize_changed=False
        self.main_hgt=None
        self.ctl_hgt=None
        self.titlebar_hgt=None
        self._wid=0
        self._hgt=0
        self._x=orig_x
        self._y=orig_y
        self.pygame_exts=["wav","mp3","ogg","xm","mod"]# Supported By pygame
        self.ffmpeg_exts=['aac','aiff','alac','ape','flac','mp3','m4a','ogg','opus','wma']# Supported By ffmpeg (That's Not Supported By pygame)
        Song_Scroll.bind("<Configure>", self.on_resize)
    def initialize(self):
        try:
            # Initialize SoundVolumeView.exe
            default_device=pyaud.get_default_output_device_info()["name"]# default_device missing ")"
            devices=self.get_devices(True)# Quit Mixer
            result=list(filter(lambda x: default_device in x, devices))
            self.Active_Device=result[0]
            if self.Active_Device=="":
                self.Active_Device="Default"
            if os.path.isfile(soundview_path):    
                soundview_device=self.Active_Device.split("(", 1)[0].replace(" ","")
                cmd=[soundview_path, "/SetDefault", soundview_device, "1", "/Unmute", soundview_device, "/SetVolume", soundview_device, str(Level.get())]
                subprocess.run(cmd, bufsize=64, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if not os.path.isfile(os.path.join(pgm_Path,"Test.mp3")):# File Created During First Ini    
                if os.path.isfile(ffmpeg_path):# Initialize ffmpeg.exe Using Test wma File    
                    fpg=FFmpeg(executable=ffmpeg_path,inputs={os.path.join(pgm_Path,"Test.wma"): None},
                            outputs={"Test.mp3": '-loglevel panic -y -b:a 320k -acodec libmp3lame -map_metadata 0'})
                    fpg.run()
            else:
                if os.path.isfile(os.path.join(pgm_Path,"Test.wma")):
                    os.remove(os.path.join(pgm_Path,"Test.wma"))       
            # Initialize Master Volumn Slider
            pygame.init()
            devices=AudioUtilities.GetSpeakers()
            interface=devices.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
            self.Master_Volume=cast(interface, POINTER(IAudioEndpointVolume))
            Level.set(5)
            self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
            pygame.mixer.init(devicename=self.Active_Device)# Choice
            self.art_lbl=Label(self.parent.song_window,image=None,background="#001829",compound="left",anchor="w")
        except Exception as ex:
            title='<Interface Initialization>'
            msg1='Initialization Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            messagebox.showerror(title, msg1+msg2)
            destroy()
    def select_output_device(self,device):
        if device==self.Active_Device:return# Same Device Selected
        try:
            pygame.mixer.quit()
            devices=self.get_devices(True)# Quit Mixer
            result=list(filter(lambda x: device in x, devices))
            self.Active_Device=result[0]
            soundview_device=self.Active_Device.split("(", 1)[0].replace(" ","")
            cmd=[soundview_path, "/SetDefault", soundview_device, "1", "/Unmute", soundview_device, "/SetVolume", soundview_device, str(Level.get())]
            subprocess.run(cmd, bufsize=64, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            title='<Change Default Audio Output Device>'
            msg1='A Program Shutdown And Restart Is Required For The\n'
            msg2='Selected Audio Output Device Settings To Update.\n'
            msg3='Do You Wish To Restart This Program Now To Update?'
            response=messagebox.askyesno(title, msg1+msg2+msg3)
            if response:destroy(True)# Restart Program
            pygame.init()
            pygame.mixer.init(devicename=self.Active_Device)# Choice
            self.play(self.key_now)
        except Exception as ex:
            title='<Audio Output Device>'
            msg1='Initialization Audio Device Failed. Ending Program!\n'
            msg2=f"Error: '{ex}'"
            msg3="Using Default Audio Device."
            messagebox.showerror(title, msg1+msg2)
            pass
    def get_devices(self,quit,capture_devices: bool = False):# False For Playback Devices, True For Capture
        pygame.mixer.init()
        devices=[]
        output_devices=sdl2_audio.get_audio_device_names(capture_devices)
        for d in output_devices:devices.append(d)
        if quit:pygame.mixer.quit()
        return devices
    def load_db_songs(self):
        art_size=json.load(open(art_path, "r+"))
        self.art_size=np.fromstring(art_size, sep="x ")
        self.Music_Count=0
        songs=json.load(open(songs_path, "r+"))
        for key,self.song in songs.items():
            if self.song not in self.Results:
                self.Results[self.Music_Count]=self.song
                self.Index.append(self.Music_Count)
                self.Music.append(self.Music_Count)
                self.Visualizer.append(self.Music_Count)    
                self.Index[self.Music_Count]=Label(self.parent.song_window,text=str(self.Music_Count+1),relief="flat",
                            anchor='w',justify="left",background="#001829",foreground="#ffffff",font=song_font)
                Index_Widgets[self.Music_Count]=self.Index[self.Music_Count]
                self.Index[self.Music_Count].grid(row=self.Music_Count, column=0, columnspan=1)
                self.Music[self.Music_Count]=Button(self.parent.song_window,bg="#001829",fg="#ffffff", font=song_font,
                            justify='center',relief='flat',command=lambda a="song",b=songs[key]:self.ctrl_btn_clicked(a,b))
                basename=os.path.basename(songs[key])
                self.Music[self.Music_Count].configure(text=os.path.splitext(basename)[0])
                Music_Widgets[self.Music_Count]=self.Music[self.Music_Count]
                self.Music[self.Music_Count].grid(row=self.Music_Count, column=1, columnspan=1)
                self.Visualizer[self.Music_Count]=Label(self.parent.song_window,text="",relief="flat",
                            anchor='w',justify="left",background="#001829",foreground="#4cffff",width=18,font=vis_font)
                Visualizer_Widgets[self.Music_Count]=self.Visualizer[self.Music_Count]
                Visualizer_Widgets[self.Music_Count].grid(row=self.Music_Count, column=2, columnspan=1)
                self.Music_Count+=1
        self.parent.song_window.update()
        self.parent.pack(side=TOP, anchor=NW,fill=BOTH, expand=True)
        self.parent.canvas.xview_moveto(0)# Position Scrollbar To Position 0 For New Table
        self.parent.canvas.yview_moveto(0)
        self.parent.canvas.update()
        if self.active_Song!="":
            Player.ctrl_btn_clicked("song",self.key_now)
    def play_external_song(self,file_path):
        file_path=file_path.replace("\\","/")
        _, file_name = os.path.split(file_path)
        file_ext=os.path.splitext(file_name)[1].replace(".","")
        song_exist=False
        if file_ext in self.pygame_exts:# Check If File Already In Database 
            songs=json.load(open(songs_path, "r"))
            for key, value in songs.items():# If Exist In Database, Set As Active Song
                if value==file_path:
                    song_exist=True
                    self.active_Song=value# Make The Database File Active
                    self.key_now=int(key)    
                    break
            if not song_exist:# If Not Exist, Add To Database, Set As Active Song
                with open(songs_path, "r") as f:
                    data=json.load(f)
                    key=len(data)
                data[str(key)]=file_path# Add a new key and value to the data
                with open(songs_path, "w") as f:# Write the updated data back to the file
                    json.dump(data, f)                
                self.active_Song=file_path# Make The New File Active
                self.key_now=int(key)    
                f.close()                        
        elif file_ext in self.ffmpeg_exts:# Convert All pygame Unsupported Files If Supported By ffmpeg
            new_file=file_path.replace(file_ext,"mp3")# Rename File Extension 
            if os.path.isfile(ffmpeg_path):# If Converter Present, Convert To mp3    
                status=Converter.convert_start(file_path,file_ext,"mp3","one_file")
                stat=list(status.keys())[0]
                value=status.get(stat)
                if value[0]==True:
                    with open(songs_path, "r") as f:
                        data=json.load(f)
                        key=len(data)
                    data[str(key)]=new_file# Add a new key and value to the data
                    with open(songs_path, "w") as f:# Write the updated data back to the file
                        json.dump(data, f)
                    self.active_Song=new_file# Make Converted File Active
                    self.key_now=int(key)    
                    f.close()                        
    def remove_db_songs(self):
        if self.active_Song=="":
            songs=json.load(open(songs_path, "r"))
            songs.clear()
            self.Check_List.clear()
            json.dump(songs,open(songs_path, "w"),indent=4)
            self.destroy_songs()
            self.parent.pack(side="top", fill="both", expand=True)
            self.parent.canvas.xview_moveto(0)# Position Scrollbar To Position 0
            self.parent.canvas.yview_moveto(0)
            self.parent.canvas.update()
    def convert_folder(self):
        if not os.path.isfile(ffmpeg_path):return    
        if self.active_Song!="":return  
        path=filedialog.askdirectory(title="Select The Folder Containing The Music Files To Convert.")
        if path=="" or path==None:return
        for ext in self.ffmpeg_exts:# Convert All pygame Unsupported Files If Supported By ffmpeg
            Converter.convert_start(path,ext,"mp3")
    def find_in_folder(self):
        if self.active_Song!="":return  
        path=filedialog.askdirectory()  
        if path=="" or path==None:return
        if os.path.isfile(ffmpeg_path):
            for ext in self.ffmpeg_exts:# Convert All pygame Unsupported Files If Supported By ffmpeg
                if ext not in self.pygame_exts:
                    files=Converter.convert_start(path,ext,"mp3")
        for root, _, files in os.walk(path):# All Files Should Be Converted By Now
            for _, name in enumerate(files):
                if name not in self.Check_List:# Prevent Duplicates
                    self.Check_List.append(name)
                else:continue    
                file_ext=os.path.splitext(name)[1].replace(".","")
                if file_ext in self.pygame_exts:
                    path=os.path.join(root, name).replace("\\","/")
                    path=path[0].upper() + path[1:]# Make Sure Drive Letter Always Capitalized
                    if path not in self.Results.values():
                        self.Results[self.Music_Count]=path
                        self.Index.append(self.Music_Count)
                        self.Music.append(self.Music_Count)    
                        self.Visualizer.append(self.Music_Count)    
                        self.Index[self.Music_Count]=Label(self.parent.song_window,text=str(self.Music_Count+1),relief="flat",
                                    anchor='w',justify="left",background="#001829",foreground="#ffffff",font=song_font)
                        Index_Widgets[self.Music_Count]=self.Index[self.Music_Count]
                        self.Index[self.Music_Count].grid(row=self.Music_Count, column=0, columnspan=1)
                        self.Music[self.Music_Count]=Button(self.parent.song_window,bg="#001829",fg="#ffffff",font=song_font, 
                            justify='center',relief='flat',command=lambda a="song",b=path:self.ctrl_btn_clicked(a,b))
                        self.Music[self.Music_Count].configure(text=os.path.splitext(name)[0])
                        Music_Widgets[self.Music_Count]=self.Music[self.Music_Count]
                        self.Music[self.Music_Count].grid(row=self.Music_Count, column=1, columnspan=1)
                        self.Visualizer[self.Music_Count]=Label(self.parent.song_window,text="",relief="flat",
                                    anchor='w',justify="left",background="#001829",foreground="#4cffff",width=18,font=vis_font)
                        Visualizer_Widgets[self.Music_Count]=self.Visualizer[self.Music_Count]
                        Visualizer_Widgets[self.Music_Count].grid(row=self.Music_Count, column=2, columnspan=1)
                        self.Music_Count+=1
            self.parent.song_window.update()
            with open(songs_path, "w") as outfile:
                json.dump(self.Results, outfile)
        outfile.close()
        self.parent.pack(side=TOP,anchor=NW,fill=BOTH,expand=True)
        self.parent.canvas.xview_moveto(0)# Position Scrollbar To Position 0 For New Table
        self.parent.canvas.yview_moveto(0)
        self.parent.canvas.update()
        return self.Results
    def play(self,key=None):
        if not bool(self.Results):return
        if key==None:key=0
        default_device=pyaud.get_default_output_device_info()["name"]# default_device missing ")"
        devices=self.get_devices(True)# Quit Mixer
        result=list(filter(lambda x: default_device in x, devices))
        self.Active_Device=result[0]
        if self.Active_Device=="":
            self.Active_Device="Default"
        pygame.mixer.init(devicename=self.Active_Device)
        if Shuffle.get() and self.repeat==False:
            shuffled=sorted(self.Results.items(), key=lambda x: random.random())
            self.Songs=dict(shuffled)
        else:self.Songs=self.Results
        for key, self.song in list(self.Songs.items())[key:]:
            self.menubar.delete(0, END)
            empty_menu=Menu(root)
            root.config(menu=empty_menu)
            Time_Now.set(0.0)
            self.time_delta=0.00
            self.paused=False
            if self.art_lbl.winfo_exists():
                self.art_lbl.config(image='')
                self.art_lbl.destroy()
                self.art=None
            if self.song:
                self.Music[key].configure(fg="#4cffff")
                self.Music[key].update()
                sound=pygame.mixer.Sound(self.song)
                song_time=sound.get_length()
                self.set_master_volume()
                self.update_time_scale(song_time)
                title_lbl.configure(text=f"Playing On {self.Active_Device}, {os.path.basename(self.song)}")
                title_lbl.update()
                self.active_Song=os.path.basename(self.song)
                self.key_now=int(key) 
                self.Vis_Time=0.00
                self.Vis_Counter=0
                if key==0:self.parent.canvas.yview_moveto((1/len(self.Results))*key)
                else:self.parent.canvas.yview_moveto((1/len(self.Results))*(key-1))# @ 2 down to show previous song
                self.parent.canvas.update()
                if np.all(self.art_size!=(0.0,0.0)):self.position_art()
                else:
                    if root.state()=="normal":
                        self._wid=root.winfo_width()
                        self._hgt=root.winfo_height()
                        self._x=root.winfo_x()
                        self._y=root.winfo_y()
                        root.geometry('%dx%d+%d+%d' % (self._wid, self._hgt, self._x, self._y))
                next_song=False
                previous_song=False
                stopped=False
                playing=True
                clicked=False
                slider_dn_time=0.00
                now_time=0.00
                pygame.mixer.music.load(self.song)
                pygame.mixer.music.play(loops=0,start=0)
                if self.last_key!=None: 
                    self.Visualizer[self.last_key].configure(text="")
                    self.Visualizer[self.last_key].update()
                self.last_key=self.key_now    
                while True and playing:
                    for event in pygame.event.get():
                        if event.type==pygame.KEYDOWN:
                            if event.key==pygame.K_p:# Pause Clicked
                                pygame.mixer.music.pause()
                            elif event.key==pygame.K_r:# UnPause Clicked
                                pygame.mixer.music.unpause()
                            elif event.key==pygame.K_n:# Next Song
                                playing=False
                                next_song=True
                                pygame.mixer.music.stop()
                                break
                            elif event.key==pygame.K_b:# Previous Song
                                playing=False
                                previous_song=True
                                pygame.mixer.music.stop()
                                break
                            elif event.key==pygame.K_s:# Stop
                                playing=False
                                next_song=False
                                previous_song=False
                                clicked=False
                                stopped=True
                                pygame.mixer.music.stop()
                                Time_Now.set(0.0)
                                break
                            elif event.key==pygame.K_c:# Song Clicked
                                playing=False
                                clicked=True
                                pygame.mixer.music.stop()
                                break
                            elif event.key==pygame.K_d:# Slider Button Down (Change Time)
                                pygame.mixer.music.pause()# Pause
                                slider_dn_time=pygame.mixer.music.get_pos()/1000
                    if not playing:break        
                    if self.paused==False:
                        now_time=(pygame.mixer.music.get_pos()/1000)+(self.time_delta+slider_dn_time)
                        self.update_timer(now_time)
                        if (now_time)>=song_time-0.1:
                            playing=False
                            self.Music[key].configure(bg="#001829",fg="#ffffff")
                            self.Music[key].update()
                            self.update_timer(0.00)
                            length=len(self.Results.items())
                            if length==1:next_song=True
                            break
                    else:self.update_timer(Time_Now.get())# Reset Time After Unpause
                    level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
                    Level.set(level*100)# Track Volume From Other Sliders (Windows, Sound Card)
                if clicked:break
                if next_song or previous_song or self.repeat==True or stopped:
                    self.Music[key].configure(bg="#001829",fg="#ffffff")
                    self.Music[key].update()
                    break
        if stopped:self.active_Song=""
        elif next_song:
            if self.key_now==len(list(self.Results))-1:
                key=0
                self.selected_song(0)
            else:self.selected_song(self.key_now+1)
        elif previous_song:
            if self.key_now==0:
                key=len(list(self.Results))-1
                self.selected_song(key)
            else:self.selected_song(self.key_now-1)
        elif self.repeat==True:
            self.selected_song(self.key_now)   
    def send_key_event(self,keyboard_key):
        if keyboard_key=="p":new_event = pygame.event.Event(KEYDOWN, unicode='p', key=K_p, mod=KMOD_NONE)# Pause
        elif keyboard_key=="r":new_event = pygame.event.Event(KEYDOWN, unicode='r', key=K_r, mod=KMOD_NONE)# Resume
        elif keyboard_key=="s":new_event = pygame.event.Event(KEYDOWN, unicode='s', key=K_s, mod=KMOD_NONE)# Song Stopped
        elif keyboard_key=="n":new_event = pygame.event.Event(KEYDOWN, unicode='n', key=K_n, mod=KMOD_NONE)# Next Song
        elif keyboard_key=="b":new_event = pygame.event.Event(KEYDOWN, unicode='b', key=K_b, mod=KMOD_NONE)# Previous Song
        elif keyboard_key=="e":new_event = pygame.event.Event(KEYDOWN, unicode='e', key=K_e, mod=KMOD_NONE)# End Song (Stop)
        elif keyboard_key=="d":new_event = pygame.event.Event(KEYDOWN, unicode='d', key=K_d, mod=KMOD_NONE)# Slider Button Down (Change Time)
        pygame.event.post(new_event)
    def ctrl_btn_clicked(self,btn,song=None):
        if btn=="play":# Play Clicked
            if Shuffle.get()==True:return
            if self.active_Song=="" and self.Music_Count>0:
                play_btn.configure(background="#00ffff")
                play_btn.update()
                shuffle_btn.configure(background="#bcbcbc")
                shuffle_btn.update()
                Shuffle.set(False)
                stop_btn.configure(background="#bcbcbc",text="Stop")
                stop_btn.update()
                Player.play(song)
            else:      
                if self.active_Song!="":
                    self.active_Song=""
                    play_btn.configure(background="#bcbcbc")
                    play_btn.update()
                    Shuffle.set(False)
                    shuffle_btn.configure(background="#bcbcbc")
                    shuffle_btn.update()
                    stop_btn.configure(background="#00ffff",text="Stopped")
                    stop_btn.update()
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    mute_btn.config(text="Mute",background="#bcbcbc")
                    mute_btn.update()
                    title_lbl.configure(text=f"Playing On  {self.Active_Device}")
                    title_lbl.update()
                    self.send_key_event("s")
        elif btn=="shuffle":# Shuffle Clicked
            if self.active_Song=="" and self.Music_Count>0:# Not Playing
                if Shuffle.get()==False: 
                    Shuffle.set(True)
                    shuffle_btn.configure(background="#00ffff")
                    shuffle_btn.update()
                    play_btn.configure(background="#bcbcbc")
                    play_btn.update()
                    stop_btn.configure(background="#bcbcbc",text="Stop")
                    stop_btn.update()
                    self.play()  
            else:# Music Playing
                if self.active_Song!="" and Shuffle.get()==False:return
                self.active_Song=""
                play_btn.configure(background="#bcbcbc")
                play_btn.update()
                Shuffle.set(False)
                shuffle_btn.configure(background="#bcbcbc")
                shuffle_btn.update()
                stop_btn.configure(background="#00ffff",text="Stopped")
                stop_btn.update()
                pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                pause_btn.update()
                mute_btn.config(text="Mute",background="#bcbcbc")
                mute_btn.update()
                title_lbl.configure(text=f"Playing On  {self.Active_Device}")
                title_lbl.update()
                self.send_key_event("s")
        elif btn=="repeat":# Shuffle Clicked
                if self.repeat==False:
                    self.repeat=True
                    repeat_btn.configure(background="#00ffff")
                    repeat_btn.update()
                else:
                    self.repeat=False   
                    repeat_btn.configure(background="#bcbcbc")
                    repeat_btn.update()
        elif btn=="stop":# Stop Clicked
            self.load_menubar(False)# Keep Mixer Initialized
            if self.active_Song!="":
                self.active_Song=""
                if self.art_lbl.winfo_exists():
                    self.art_lbl.config(image='')
                    self.art_lbl.destroy()
                self.art=None
                play_btn.configure(background="#bcbcbc")
                play_btn.update()
                shuffle_btn.configure(background="#bcbcbc")
                shuffle_btn.update()
                Shuffle.set(False)
                stop_btn.configure(background="#00ffff",text="Stopped")
                stop_btn.update()
                pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                pause_btn.update()
                repeat_btn.configure(background="#bcbcbc")
                repeat_btn.update()
                mute_btn.config(text="Mute",background="#bcbcbc")
                mute_btn.update()
                title_lbl.configure(text=f"Playing On  {self.Active_Device}")
                title_lbl.update()
                self.send_key_event("s")
        elif btn=="pause":# Pause Clicked
            if self.active_Song!="":
                if pause_btn.cget("text")=="Pause":
                    self.paused=True
                    pause_btn.configure(text="Unpause",background="#00ffff")# Resume
                    pause_btn.update()
                    self.send_key_event("p")
                elif pause_btn.cget("text")=="Unpause":# Resume Clicked
                    self.paused=False
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    self.send_key_event("r")
        elif btn=="song"and song!=None:# Song Clicked
            if self.active_Song!="":
                Time_Now.set(0.0)
                self.Music[self.key_now].configure(bg="#001829",fg="#ffffff")
                self.Music[self.key_now].update()
                self.active_Song=""
                stop_btn.configure(background="#00ffff",text="Stopped")
                stop_btn.update()
                title_lbl.configure(text=f"Playing On  {self.Active_Device}")
                title_lbl.update()
            if self.active_Song=="":
                if Shuffle.get()!=True:
                    play_btn.configure(background="#00ffff")
                    play_btn.update()
                stop_btn.configure(background="#bcbcbc",text="Stop")
                stop_btn.update()
                for index, value in self.Results.items():
                    if isinstance(song, int):# Song Is Key
                        if index==song:
                            key=index
                            break
                    else:# Song Is Value    
                        if value==song:
                            key=index
                            break
                self.play(key)
        elif btn=="next":# Next Clicked
            if self.active_Song!="":
                if self.repeat==True:
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    self.selected_song(self.key_now)
                else:    
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    self.send_key_event("n")
            elif self.active_Song=="" and self.Music_Count>0:# Same As Clicking Play Button
                play_btn.configure(background="#00ffff")
                play_btn.update()
                shuffle_btn.configure(background="#bcbcbc")
                shuffle_btn.update()
                Shuffle.set(False)
                stop_btn.configure(background="#bcbcbc",text="Stop")
                stop_btn.update()
                Player.play(song)
        elif btn=="previous":# Precious Clicked
            if self.active_Song!="":
                if self.repeat==True:
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    self.selected_song(self.key_now)
                else:    
                    pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
                    pause_btn.update()
                    self.send_key_event("b")
        elif btn=="mute":# Mute Clicked
            if self.active_Song!="":
                txt=mute_btn.cget("text")
                if txt=="Mute":
                    self.Master_Volume.SetMute(True, None)
                    mute_btn.config(text="UnMute",background="#00ffff")
                    mute_btn.update()    
                elif txt=="UnMute":# Unmute Clicked
                    self.Master_Volume.SetMute(False, None)
                    mute_btn.config(text="Mute",background="#bcbcbc")
                    mute_btn.update()
        elif btn=="quit":# Quit Clicked
            pygame.mixer.quit()
            pygame.QUIT
            self.active_Song=""
            destroy()
    def slider_down(self,event):
        if self.active_Song=="":return
        self.paused=True
        self.send_key_event("d")
    def slider_up(self,event):
        if self.active_Song=="":return
        pause_btn.configure(text="Pause",background="#bcbcbc")# Pause
        pause_btn.update()
        pygame.mixer.music.play(loops=0,start=Time_Now.get())        
        pygame.mixer.music.unpause()# Resume Clicked
        self.paused=False
    def slider_changing(self,event):
        if self.active_Song=="":
            Time_Now.set(0.00)
            return
        self.time_delta=(Time_Now.get()-pygame.mixer.music.get_pos()/1000)# Changing Slider vs Time At Paused
    def selected_song(self,key=None):
        if key==None:
            pygame.mixer.music.stop()
            self.update_timer(0.00)    
            for index, value in self.Results.items():
                if value==self.song_selected:
                    key=index
                    break
            self.Music[key].configure(bg="#001829",fg="#ffffff")
            self.Music[key].update()
            self.song_selected=""
            self.active_Song=""
            self.play(key)
        else:
            self.song_selected=""
            self.active_Song=""
            pygame.mixer.music.stop()
            self.update_timer(0.00)
            self.play(key)
    def get_volume(self):
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        return level*100
    def update_time_scale(self,sec):
        if sec>=20:sec=int(round((sec),3))+1
        mods={8:sec%8,9:sec%9,10:sec%10,11:sec%11,12:sec%12,13:sec%13,14:sec%14,15:sec%15,16:sec%16,17:sec%17,18:sec%18,}
        interval=round(sec/min(mods,key=mods.get),2)# Set Lowest Modulo For Intervals
        time_scale.config(from_=0.0,to=sec)
        time_scale.config(tickinterval=(interval))
        time_scale.config(resolution=0.01)
        time_scale.update()
    def set_master_volume(self):
        self.Master_Volume.SetMasterVolumeLevelScalar(Level.get()/100, None)
        level=self.Master_Volume.GetMasterVolumeLevelScalar()# Volume Slider Level / 100
        if level==0:self.Master_Volume.SetMute(True, None)
        else:self.Master_Volume.SetMute(False, None)
    def update_timer(self,time):
        Time_Now.set(time)
        time_scale.update()
        if time==0.0:
            self.Vis_Counter=0
            self.Vis_Time=0.00
        vis_txt=["♩"," ♩","  ♫","   ♬","    ♩","     ♩","      ♫","       ♬","        ♩","         ♩",
                "          ♫","           ♬","            ♩","             ♩","              ♫",
                "               ♬","                ♩","                 ♩","                  ♫",
                "                   ♬","                    ♩","                     ♩","                      ♫",
                "                       ♬","                        ♩","                         ♩",
                "                          ♫","                           ♬","                            ♩",
                "                             ♩","                              ♫","                               ♬"]
        if Time_Now.get()>=self.Vis_Time+0.17:
            if self.Vis_Counter>=32:self.Vis_Counter=0
            self.Vis_Time=time
            self.Visualizer[self.key_now].configure(text=vis_txt[self.Vis_Counter])
            self.Visualizer[self.key_now].update()
            self.Vis_Counter+=1
        elif Time_Now.get()<self.Vis_Time:
            if self.Vis_Counter<=0:self.Vis_Counter=32
            self.Vis_Counter-=1
            self.Vis_Time=time
            self.Visualizer[self.key_now].configure(text=vis_txt[self.Vis_Counter])
            self.Visualizer[self.key_now].update()
    def destroy_songs(self):# Destroys All Window Widgets
        if self.active_Song=="":
            try:
                if self.art_lbl.winfo_exists():# Destroy Album Art Label And Image
                    self.art_lbl.config(image='')
                    self.art_lbl.destroy()
                for c in range(len(Music_Widgets)):
                        Index_Widgets[c].destroy()
                        Music_Widgets[c].destroy()
                        Visualizer_Widgets[c].destroy()
                self.Music_Count=0
                self.Results.clear()
            except Exception:pass
    def get_song_art(self,song_file,ext):
        try:
            image_file=None
            if ext=="mp3":
                audio_file=eyed3.load(song_file)
                for i in audio_file.tag.images:# Iterate through all images in the MP3 file
                    image_file=open(f"Album_Art {i.picture_type}.jpg", "wb")
                    image_file.write(i.image_data)
                    im=Image.open(image_file.name)
                    im.thumbnail(self.art_size)
                    im.save(f"Album_Art {i.picture_type}.jpg")
                    thumbnail=ImageTk.PhotoImage(Image.open(f"Album_Art {i.picture_type}.jpg"))
                    image_file.close()
                    if os.path.exists(f"Album_Art {i.picture_type}.jpg"):os.remove(f"Album_Art {i.picture_type}.jpg")
                if image_file==None:# Display Blank Image
                    im=Image.open(blank_image)
                    im.thumbnail(self.art_size)
                    im.save("Album_Art No Art.jpg")
                    thumbnail=ImageTk.PhotoImage(Image.open("Album_Art No Art.jpg"))
                    im.close()
                    if os.path.exists("Album_Art No Art.jpg"):os.remove("Album_Art No Art.jpg")
            elif ext=="wav":
                tags=mutagen.File(song_file)# Read the tags from the WAV file
                if 'APIC:' in tags:# Get the album art (if available)
                    image_file=tags['APIC:'].data
                    with open('Album_Art.jpg', 'wb') as f:
                        f.write(image_file)
                    im=Image.open('Album_Art.jpg')
                    im.thumbnail(self.art_size)
                    im.save('Album_Art.jpg')
                    thumbnail=ImageTk.PhotoImage(Image.open('Album_Art.jpg'))
                    f.close()
                    if os.path.exists('Album_Art.jpg'):os.remove('Album_Art.jpg')
                else:    
                    if image_file==None:# Display Blank Image
                        im=Image.open(blank_image)
                        im.thumbnail(self.art_size)
                        im.save("Album_Art No Art.jpg")
                        thumbnail=ImageTk.PhotoImage(Image.open("Album_Art No Art.jpg"))
                        im.close()
                        if os.path.exists("Album_Art No Art.jpg"):os.remove("Album_Art No Art.jpg")
            else:    
                im=Image.open(blank_image)
                im.thumbnail(self.art_size)
                im.save("Album_Art No Art.jpg")
                thumbnail=ImageTk.PhotoImage(Image.open("Album_Art No Art.jpg"))
                im.close()
                if os.path.exists("Album_Art No Art.jpg"):os.remove("Album_Art No Art.jpg")
            return thumbnail    
        except Exception:
            return None
    def position_art(self):
        try:
            if self.art!=None:self.art_lbl.destroy()# If Art Exist Destroy
            # Adjust root and canvas To Accommodate Music Image & Place Image 
            self.index_info=self.parent.song_window.grid_bbox(row=self.key_now, column=0,)
            self.song_info=self.parent.song_window.grid_bbox(row=self.key_now, column=1,)
            self.vis_info=self.parent.song_window.grid_bbox(row=self.key_now, column=2,)
            extra_width=0.05*screen_width
            self._wid=int(self.index_info[2]+self.song_info[2]+self.vis_info[2]+self.art_size[0]+extra_width)
            if self._wid>=screen_width:self._wid=screen_width-50
            self.main_hgt=main_frame.winfo_reqheight()
            self.ctl_hgt=ctrl_frame.winfo_reqheight()
            self.titlebar_hgt=root.winfo_toplevel().winfo_y()
            extra_hgt=0.0065*screen_height
            allowed_height=int(self.art_size[1]+self.main_hgt+self.ctl_hgt+taskbar_height+abs(self.titlebar_hgt)+extra_hgt)
            if allowed_height>screen_height:# Art Size Too Large, Adjust Art Size For Screen Resolution
                if np.all(self.art_size!=(0.0,0.0)):
                    if self.art_size[0]==600.0:
                        if allowed_height-100<=screen_height:
                            self.art_size=(500.0,500.0)
                        elif allowed_height-200<=screen_height:
                            self.art_size=(400.0,400.0)
                        elif allowed_height-300<=screen_height:
                            self.art_size=(300.0,300.0)
                    elif self.art_size[0]==500.0:
                        if allowed_height-100<=screen_height:
                            self.art_size=(400.0,400.0)
                        elif allowed_height-200<=screen_height:
                            self.art_size=(300.0,300.0)
                    elif self.art_size[0]==400.0:
                        if allowed_height-100<=screen_height:
                            self.art_size=(300.0,300.0)
                        elif allowed_height-200<=screen_height:
                            self.art_size=(200.0,200.0)
            song=self.Songs.get(self.key_now)
            file_ext=os.path.splitext(self.active_Song)[1].replace(".","")
            if file_ext in self.pygame_exts:self.art=self.get_song_art(song,file_ext)
            if root.state()=='normal':
                self._canvas_hgt=int((self.art_size[1]/(self.vis_info[3]))*self.vis_info[3])+extra_hgt
                self.parent.canvas.configure(height=self._canvas_hgt)
                self._hgt=int(self._canvas_hgt+self.main_hgt+self.ctl_hgt)
                if self._x==int(orig_x) or self.artsize_changed:# Startup Center Screen
                    self._x=int((screen_width/2)-(self._wid/2))
                    self._y=int((screen_height/2)-(self._hgt/2)-taskbar_height)
                else:self._x,self._y=(int(s) for s in root.geometry().split("+")[1:])# X,Y Positions Were Changed    
                root.geometry('%dx%d+%d+%d' % (self._wid, self._hgt, self._x, self._y))
                self.artsize_changed=False
                self.Vis_Widgets=int(self._canvas_hgt/self.vis_info[3])# Visible Widgets (Rows) Showing On Canvas
                num_songs=len(self.Songs)-1
                if self.key_now==0:_row=0
                elif num_songs<=self.Vis_Widgets:_row=0
                elif num_songs>self.Vis_Widgets:
                    for r in range(0,self.Vis_Widgets):
                        if self.key_now==num_songs-r:# After Crossover Point
                            _row=self.key_now-(self.Vis_Widgets-(r+1))
                            break
                        else: _row=self.key_now-1# Before Crossover Point
                if self.key_now!=0:            
                    if self.key_now-1==num_songs-self.Vis_Widgets:_row-=1# Right At The Point Of Crossover
                self.art_lbl=Label(self.parent.song_window,image=self.art,background="#001829",compound="left",anchor="nw")
                self.art_lbl.grid(rowspan=self.Vis_Widgets,row=_row, column=3, columnspan=10,sticky="w")
                self.parent.song_window.update()
                if self.key_now==0:self.parent.canvas.yview_moveto((1/len(self.Results))*self.key_now)
                else:self.parent.canvas.yview_moveto((1/len(self.Results))*(self.key_now-1))# @ 2 down to show previous song
                self.parent.canvas.update()
            elif root.state()=='zoomed':
                self._canvas_hgt=self.parent.canvas.winfo_height()
                self.vis_info=self.parent.song_window.grid_bbox(row=self.key_now, column=2,)
                vis_hgt=self.vis_info[3]# x,y,wid,hgt
                self.Vis_Widgets=round(self._canvas_hgt/vis_hgt)
                num_songs=len(self.Songs)-1
                if num_songs<=self.Vis_Widgets:
                    key=0
                    _row=0
                else:    
                    if self.key_now==0 or self.key_now==1:
                        key=0
                        _row=0
                    elif self.key_now<=len(self.Results)-self.Vis_Widgets:
                        key=self.key_now-1
                        _row=key
                    else:
                        key=self.key_now-1
                        _row=len(self.Results)-self.Vis_Widgets
                _rowspan=int(round(self.art_size[1]/vis_hgt))    
                self.art_lbl=Label(self.parent.song_window,image=self.art,background="#001829",compound="left",anchor="nw")
                self.art_lbl.grid(rowspan=_rowspan,row=_row,column=3,columnspan=10,sticky="w")
                self.parent.song_window.update()
                self.parent.canvas.yview_moveto((1/len(self.Results))*(key))
                self.parent.canvas.update()
        except Exception as e:# Set Default Geometry
                self._x=root.winfo_x()
                self._y=root.winfo_y()
                self._canvas_hgt=int(self._canvas_hgt-self.art_size[1])
                self.parent.canvas.configure(height=100)
                root.geometry('%dx%d+%d+%d' % (root_width, root_height, self._x, self._y, ))
    def on_resize(self,event=None):
        if np.all(self.art_size==(0.0,0.0)):# No Art
            if self.art!=None:
                self.art_lbl.destroy()
        song_font['size']=12
        vis_font['size']=16
        if root.state()=='zoomed':
            button_font['size']=12
        elif root.state()=='normal':
            button_font['size']=10
            if np.all(self.art_size==(0.0,0.0)):# No Art
                self._wid=root.winfo_width()
                self._hgt=root.winfo_height()
                self._x=root.winfo_x()
                self._y=root.winfo_y()
    def insert_mp3_art(self):
        try:# Load the MP3 file
            types=[('MP3 Music Files', '*.mp3')] 
            path=filedialog.askopenfile(mode='r',defaultextension=".mp3",filetypes=types,title="Please Select A MP3 Music File For Album Art Insertion!")
            if path==None:return
            song_path=path.name
            audiofile = eyed3.load(song_path)
            audiofile.initTag()# Initialize the ID3 tag
        except Exception:
            pass
        try:#Get Music File Art Path. Replace jpg with png if your image is in PNG format
            types=[('JPG Image Files', '*.jpg')] 
            path=filedialog.askopenfile(mode='r',defaultextension=".jpg",filetypes=types,title=f"Please Select A JPG Image File To Insert Into {os.path.basename(song_path)}! Image File Sizes Should Be @ 600 x 600.")
            if path==None:return
            art_path=path.name
            audiofile.tag.images.set(ImageFrame.FRONT_COVER, open(art_path, 'rb').read(), 'image/jpeg')# Set the album art (cover image)
            audiofile.tag.save()# Save the changes
        except Exception:
            pass
    def select_art_res(self,resolution):
        if resolution=="No Art":resolution="0 x 0"
        art=json.load(open(art_path, "r"))
        json.dump(art,open(art_path, "w"),indent=4)
        with open(art_path, "w") as outfile:
            json.dump(resolution, outfile)# Write The Selected Resolution To .json art File
        outfile.close()
        size=np.fromstring(resolution, sep="x ")# Convert resolution String To Numpy Array
        if np.all(size==self.art_size):self.artsize_changed=False # Compare Old And New Arrays For Change
        else:self.artsize_changed=True# If Changed, Window Get Re-Centered On Next Music File.  
        self.art_size=size
    def load_menubar(self,quit):
        self.menubar=Menu(root,fg="#000000")# Create Menubar
        music_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label='  Select/Convert Music ',menu=music_menu)
        music_menu.add_command(label='Upload Music From Folder',command=lambda:Player.find_in_folder())
        music_menu.add_separator()
        music_menu.add_command(label='Remove All Music',command=lambda:Player.remove_db_songs())
        music_menu.add_separator()
        music_menu.add_command(label='Convert Music in Folder To MP3',command=lambda:Player.convert_folder())
        tag_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label=' Edit Music Art ',menu=tag_menu)
        tag_menu.add_command(label='Insert Album Art Into MP3 File',command=lambda:Player.insert_mp3_art())
        tag_menu.add_separator()
        mp3tag=Menu(self.menubar,background='aqua',foreground='black',tearoff=0) # SubMenu
        mp3tag.add_command(label='Edit Tags Using Mp3tag',command=lambda:open_mp3tag())
        tag_menu.add_cascade(label='Mp3tag',menu=mp3tag)
        art_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label=' Select Displayed Art Size ',menu=art_menu)
        resolutions=["600 x 600","500 x 500","400 x 400","300 x 300","200 x 200","100 x 100","No Art"]
        for r in range(len(resolutions)):
            art_menu.add_command(label=resolutions[r],command=lambda x=resolutions[r]:Player.select_art_res(x))
            art_menu.add_separator()
        if not os.path.isfile(ffmpeg_path):    
            music_menu.entryconfig('Convert Music In Folder To MP3', state="disabled")
        if os.path.isfile(soundview_path):
            devices=Player.get_devices(quit)
            device_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)
            self.menubar.add_cascade(label=' Select Audio Output Device ',menu=device_menu)
            for d in range(len(devices)):
                device_menu.add_command(label=devices[d],command=lambda x=devices[d]:Player.select_output_device(x))
                device_menu.add_separator()
            svv=Menu(self.menubar,background='aqua',foreground='black',tearoff=0) # SubMenu
            svv.add_command(label="View / Configure All Devices",command=lambda:open_soundview())
            device_menu.add_cascade(label='SoundVolumeView',menu=svv)
        bluetooth_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label=' Bluetooth ',menu=bluetooth_menu)
        bluetooth_menu.add_command(label='Turn Bluetooth "ON"',command=lambda:asyncio.run(bluetooth_power(True)))
        bluetooth_menu.add_separator()
        bluetooth_menu.add_command(label='Turn Bluetooth "OFF"',command=lambda:asyncio.run(bluetooth_power(False)))
        root.config(menu=self.menubar)
        about_menu=Menu(self.menubar,background='aqua',foreground='black',tearoff=0)# File Menu and commands
        self.menubar.add_cascade(label=' About ',menu=about_menu)
        about_menu.add_command(label='About My Music Player',command=lambda:about())
class XY_Scroll(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent)
        self.config(bg="#001829",relief="sunken",borderwidth=6)
        self.pack(padx=(0,0),pady=(0,0))
        self.canvas=tk.Canvas(self,bg="#001829",height=100)
        scrollstyle=ttk.Style()
        scrollstyle.theme_use('classic')
        self.vbar=ttk.Scrollbar(self,orient='vertical',command=self.canvas.yview)
        self.vbar.pack(side=RIGHT,fill=Y,padx=(2,2),pady=(0,20))                                        
        self.hbar=ttk.Scrollbar(self, orient="horizontal", command=self.canvas.xview)
        self.hbar.pack(side=BOTTOM,fill=X,padx=(2,2),pady=(0,3))
        self.canvas.pack(side=TOP, anchor=NW, fill=BOTH, expand=True, padx=(0,0), pady=(0,0))
        self.song_window=tk.Frame(self.canvas,bg="#001829")
        self.song_window.pack(side=TOP,anchor=NW,fill=BOTH, expand=True, padx=(0,0), pady=(0,0))                     
        self.canvas.configure(xscrollcommand=self.hbar.set,yscrollcommand=self.vbar.set)                          
        self.canvas_window=self.canvas.create_window((0,0),window=self.song_window,anchor=NW,tags="self.song_window") 
        self.canvas.update
        self.canvas.bind("<Key-Prior>", self.page_up)
        self.canvas.bind("<Key-Next>", self.page_down)
        self.canvas.bind("<Key-Up>", self.unit_up)
        self.canvas.bind("<Key-Down>", self.unit_down)        
        self.canvas.bind("<Key-Left>", self.unit_left)
        self.canvas.bind("<Key-Right>", self.unit_right)        
        self.song_window.bind("<Configure>", self.rst_frame)                       
        self.song_window.bind('<Enter>', self.inside_canvas)                                 
        self.song_window.bind('<Leave>', self.outside_canvas)
        self.rst_frame(None)
    def rst_frame(self, event):                                              
        self.canvas.configure(scrollregion=self.canvas.bbox(ALL))                 
    def unit_up(self, event):
        self.canvas.yview_scroll(-1, "unit")
        return "break"
    def unit_down(self, event):
        self.canvas.yview_scroll(1, "unit")
        return "break"
    def unit_left(self, event):
        self.canvas.xview_scroll(-1, "unit")
        return "break"
    def unit_right(self, event):
        self.canvas.xview_scroll(1, "unit")
        return "break"
    def page_up(self, event):
        self.canvas.yview_scroll(-1, "page")
        return "break"
    def page_down(self, event):
        self.canvas.yview_scroll(1, "page")
        return "break"
    def scroll_mousey(self, event):
        self.canvas.yview_scroll(int(-1* (event.delta/120)), 'units')
    def inside_canvas(self, event):                                                       
        self.canvas.focus_set()                                                 
        self.canvas.bind_all("<MouseWheel>", self.scroll_mousey)
    def outside_canvas(self, event):                                                       
        self.canvas.unbind_all("<MouseWheel>")
async def bluetooth_power(turn_on):
    result=0
    all_radios = await radios.Radio.get_radios_async()
    for this_radio in all_radios:
        if this_radio.kind == radios.RadioKind.BLUETOOTH:
            if turn_on:
                msg1="Before Continuing, Make Sure That Your Bluetooth\n"
                msg2="Devices Are Turned On And Discoverable In Your System\n"
                msg3="As An Available Bluetooth Device. After This Program\n"
                msg4='Restarts, Select The Desired Bluetooth Device In The\n'
                msg5='"Select Audio Output Device" Menu.'
                msg=msg1+msg2+msg3+msg4+msg5
                proceed=messagebox.askokcancel("<Bluetooth Radio Power>",msg)
                if proceed:result=await this_radio.set_state_async(radios.RadioState.ON)
            else:
                result=await this_radio.set_state_async(radios.RadioState.OFF)
            if result==1:destroy(True)# Restart Program    
def open_mp3tag():
    if os.path.isfile(mp3tag_path):
        root.withdraw()
        process=subprocess.Popen([mp3tag_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        process.wait()
        root.deiconify()
        root.grab_set()
        root.focus_force()
        root.update()
def open_soundview():
    if os.path.isfile(soundview_path):
        root.withdraw()
        process=subprocess.Popen([soundview_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        process.wait()
        root.deiconify()
        root.grab_set()
        root.focus_force()
        root.update()
def about():
    msg1='Creator: Ross Waters\nEmail: RossWatersjr@gmail.com\nLanguage: Python version 3.12.0 64-bit\n'
    msg2='Revision: 4.8\nRevision Date: 03/17/2024\nCreated For Windows 10/11'
    msg=msg1+msg2
    messagebox.showinfo('About My Music Player', msg)
def destroy(restart=None):
    try:# X Icon Was Clicked
        pygame.quit()
        pygame.QUIT
        pyaud.terminate()
        Player.destroy_songs()
        for widget in root.winfo_children():# Destroys Menu Bars, Frame, Canvas And Scroll Bars
            if isinstance(widget, tk.Canvas):widget.destroy()
            else:widget.destroy()
        if restart!=None:
            os.execl(sys.executable, os.path.abspath(__file__), *sys.argv)
        else:os._exit(0)
    except Exception:pass
    os._exit(0)
def get_clicked_song():# This Application Must Be Selected As Default Media Player For The Desired Extensions
    exts=['*.wav','*.mp3','*.ogg','*.xm','*.mod','*.wma','*.flac','*.m4a','*.aac','*.alac','*.opus','*.ape','*.aiff']
    songs_clicked=[]
    time_stamps=[]
    for e in range(len(exts)):
        try:
            music_files=glob.glob(os.path.join(os.path.expanduser("~"),'Music','**','*'+exts[e]), recursive=True)
            last_music_file=max(music_files, key=os.path.getatime)
            last_music_path=os.path.abspath(last_music_file)
            timestamp=os.path.getatime(Path(last_music_path))
            songs_clicked.append(last_music_path)
            time_stamps.append(timestamp)
            if e>=1:
                if time_stamps[e]>time_stamps[e-1]:
                    recent_song=songs_clicked[e]
                    recent_time=time_stamps[e]
                else:
                    recent_song=songs_clicked[e-1]
                    recent_time=time_stamps[e]
        except Exception:pass
    now_time=time.time()
    if now_time>recent_time+7:# If Lapsed Time > 7 Seconds Then Ignore
        return None# No Recent Songs Selected In File Explorer Within 5 Seconds
    else:
        try:# Close File Explorer If Still Opened
            [process.kill() for process in psutil.process_iter() if process.name() == "explorer.exe"]    
        except Exception:pass
        return recent_song# Return Selected Song From File Explorer For Playing
if __name__ == '__main__':
    music_clicked=get_clicked_song()# Music File Clicked In File Explorer Started Application
    root=tk.Tk()
    style=ttk.Style()
    style.theme_use('classic')
    primary_monitor = MonitorFromPoint((0, 0))
    monitor_info = GetMonitorInfo(primary_monitor)
    monitor_area = monitor_info.get("Monitor")
    work_area = monitor_info.get("Work")
    taskbar_height = monitor_area[3] - work_area[3]
    screen_width=root.winfo_screenwidth() # Width of the screen
    screen_height=root.winfo_screenheight() # Height of the screen
    ratio=screen_width/screen_height
    root_height=screen_height*0.5
    root_width=ratio*root_height
    orig_x=(screen_width/2)-(root_width/2)
    orig_y=(screen_height/2)-(root_height/2)-taskbar_height
    root.geometry('%dx%d+%d+%d' % (root_width, root_height, orig_x, orig_y, ))
    root.configure(bg="#001829")
    button_font=font.Font(family='Times New Romans', size=10, weight='bold', slant='italic')
    song_font=font.Font(family='Times New Romans', size=12, weight='normal', slant='italic')
    vis_font=font.Font(family='Times New Romans', size=16, weight='normal', slant='roman')
    root.protocol("WM_DELETE_WINDOW", destroy)
    pgm_Path=Path(__file__).parent.absolute()
    ffmpeg_path=os.path.join(pgm_Path, "ffmpeg.exe")
    soundview_path=os.path.join(pgm_Path, "SoundVolumeView.exe")
    mp3tag_path=os.path.join(pgm_Path, "Mp3tag.exe")
    ico_path=os.path.join(pgm_Path, 'music_player.ico')
    songs_path=os.path.join(Path(__file__).parent.absolute(),"songs.json")
    art_path=os.path.join(Path(__file__).parent.absolute(),"art.json")
    blank_image=os.path.join(Path(__file__).parent.absolute(),"No Art.jpg")
    root.iconbitmap(default=ico_path)# root and children
    root.title("My Music Player")
    Music_Widgets={}# widgets For Destruction
    Visualizer_Widgets={}# widgets For Destruction
    Index_Widgets={}
    Time_Now=DoubleVar()# Time Meter
    Level=DoubleVar()# Volume Meter
    Shuffle=BooleanVar()# Shuffle Play
    Shuffle.set(False)
    Song_Scroll=XY_Scroll(root) # Vertical/Horizontal Scrollbar Window
    Song_Scroll.pack(side=TOP, anchor=NW, fill=BOTH, expand=True, padx=(10,10), pady=(0,0))
    pyaud=pyaudio.PyAudio()
    Player=Audio_Player(Song_Scroll)
    Player.initialize()
    Player.load_menubar(True)
    title_skin=tk.PhotoImage(file=os.path.join(pgm_Path, '1280x40.png'))
    btn_skin=tk.PhotoImage(file=os.path.join(pgm_Path, '400x40.png'))
    main_frame=tk.Frame(root,relief="sunken",borderwidth=5)
    main_frame.pack(side=TOP,anchor=NW,fill=X, expand=False, padx=(10,10), pady=(0,12))
    main_frame.config(bg="#0b5394")
    title_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    title_frame.pack(side=TOP,anchor=NW,fill=X, expand=True, padx=(3,3), pady=(3,3))
    title_frame.config(bg="#000000")
    pix_wid=int(root_width*0.17) #Make Width 17% Of Root Width Using Label image=tk.PhotoImage(),Zero Image 
    volume_lbl=tk.Button(title_frame,text='Master Volume',image=btn_skin, compound="center",width=pix_wid-5,height=20,
                background="#bcbcbc",foreground="#000000",font=button_font,justify="center",relief='sunken',borderwidth=5)
    volume_lbl.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    title_lbl=tk.Button(title_frame,text="",image=title_skin, compound="center",height=20,
                    background="#aeaeae",foreground="#000000",font=button_font,justify="center",relief='sunken',borderwidth=5)
    title_lbl.pack(side=RIGHT,anchor=NE,fill=BOTH,expand=True,padx=(5,3), pady=(3,3))
    slider_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    slider_frame.pack(side=TOP,anchor=NW,fill=BOTH, expand=False, padx=(3,3), pady=(0,3))
    slider_frame.config(bg="#000000")
    volume=tk.Scale(slider_frame, variable=Level, from_=0,to=100, orient='horizontal', resolution=1, 
                    tickinterval=50,showvalue=1,borderwidth=5,relief="sunken",font=button_font,
                    length=pix_wid,bg="#aeaeae", fg="#000000",troughcolor="#001829", activebackground="#0061aa",
                    highlightthickness=0,command=lambda event:Player.set_master_volume())
    volume.pack(side=LEFT,anchor=NW,fill=BOTH, expand=False, padx=(3,0), pady=(3,3))
    time_scale=tk.Scale(slider_frame, variable=Time_Now, relief="sunken", orient='horizontal',resolution=0.01,
                        bg="#aeaeae",borderwidth=5,font=button_font,fg="#000000",troughcolor="#001829",  
                        activebackground="#0061aa",highlightthickness=0,command=lambda event:Player.slider_changing(event))
    time_scale.pack(side=LEFT,anchor=NW,fill=BOTH,expand=True, padx=(5,3), pady=(3,3))
    time_scale.bind("<Button-1>",lambda event:Player.slider_down(event))
    time_scale.bind("<ButtonRelease-1>",lambda event:Player.slider_up(event))
    ctrl_frame=tk.Frame(main_frame,relief="sunken",borderwidth=3)
    ctrl_frame.pack(side=RIGHT,anchor=NE,fill=BOTH, expand=True, padx=(3,3), pady=(0,3))
    ctrl_frame.config(bg="#000000")
    quit_btn=tk.Button(ctrl_frame,text="Quit",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("quit"))
    quit_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,3), pady=(3,3))
    stop_btn=tk.Button(ctrl_frame,text="Stop",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("stop"))
    stop_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    mute_btn=tk.Button(ctrl_frame,text="Mute",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("mute"))
    mute_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    repeat_btn=tk.Button(ctrl_frame,text="Repeat",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("repeat"))
    repeat_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    pause_btn=tk.Button(ctrl_frame,text="Pause",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("pause"))
    pause_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    next_btn=tk.Button(ctrl_frame,text="Next",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=4,height=20,command=lambda:Player.ctrl_btn_clicked("next"))
    next_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    previous_btn=tk.Button(ctrl_frame,text="Previous",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("previous"))
    previous_btn.pack(side=RIGHT,fill=X, expand=True, padx=(5,5), pady=(3,3))
    shuffle_btn=tk.Button(ctrl_frame,text="Shuffle All",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("shuffle"))
    shuffle_btn.pack(side=RIGHT,fill=X, expand=True, padx=(0,0), pady=(3,3))
    play_btn=tk.Button(ctrl_frame,text="Play All",foreground="#000000",image=btn_skin, compound="center",font=button_font,relief="sunken",
                       background="#bcbcbc",borderwidth=5,activeforeground="#4cffff",width=1,height=20,command=lambda:Player.ctrl_btn_clicked("play"))
    play_btn.pack(side=RIGHT,fill=X, expand=True, padx=(3,5), pady=(3,3))
    Converter=Audio_Converter()
    if music_clicked!=None:Player.play_external_song(music_clicked)
    root.after(500, Player.load_db_songs())
    root.mainloop()
