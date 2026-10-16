// Antresoli SX 0.8 pattern architecture, Chain+ and envelope safety - standalone acid sequencer / live performance, SDL2, C11
#include <SDL.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <errno.h>

#define SR 48000
#define STEPS 16
#define BANKS 128
#define CHAINS 128
#define MAX_PATTERNS 32
#define MAX_BARS 128
#define PI 3.14159265358979323846
#define CLAMP(v,lo,hi) ((v)<(lo)?(lo):((v)>(hi)?(hi):(v)))

typedef struct { int note, on, accent, slide, velocity, gate, cutoff_lock; } Step;
typedef struct {
  Step step[STEPS];
  int bpm, cutoff, resonance, decay, envmod, drive, wave;
} Pattern;
typedef struct {
  Pattern pat;
  Pattern play_pat; /* audio-owned snapshot; independent from the editor */
  Pattern bank[BANKS];
  int active, bank_select, chain[CHAINS], chain_len, chain_pos, play_chain_pos, play_slot, chain_enabled, chain_cursor;
  double phase, freq, target, env, filter_env, lp1, lp2, lp3, lp4;
  double amp_env; int amp_stage; /* 0 off, 1 attack, 2 decay, 3 sustain, 4 release */
  int running, pos, current, playing, page, step_edit, step_field, last_note, chain_plus, chain_minus;
  int project_bpm, menu, menu_cursor, tool_cursor, preset_cursor, seq_cursor, live_param, sound_param, custom_sound, custom_seq;
  int dirty, scale_lock, root_note, scale_type, project_field, queued_pattern, queued_on, last_error;
  int library_type, library_slot, library_confirm;
  int pattern_count, edit_pattern, edit_bar, play_pattern, play_bar;
  int chain_items[CHAINS], chain_size, chain_on, playlist_cursor, chain_field, init_confirm;
  int attack, sustain, release, filter_fm, slide_time, mod_rate, mod_depth, filter_mode;
  double amp_level, lfo_phase;
  unsigned int noise_seed;
  double tri;
  double samples_to_step;
  uint64_t frame;
  SDL_AudioDeviceID dev;
  SDL_AudioSpec actual;
} Synth;
static Synth syn;
/* Separate patterns (songs) from bars (pages) and playlist entries.
   Static allocation keeps addresses stable across SDL audio callbacks. */
static Pattern pattern_grid[MAX_PATTERNS][MAX_BARS];
static int bar_counts[MAX_PATTERNS];
static void publish_bar(Synth *s){
  pattern_grid[s->edit_pattern][s->edit_bar]=s->pat;
}
static void select_bar(Synth *s,int bar){
  publish_bar(s);
  s->edit_bar=CLAMP(bar,0,bar_counts[s->edit_pattern]-1);
  s->pat=pattern_grid[s->edit_pattern][s->edit_bar];
  s->current=bar<0?0:s->current;
  s->chain_plus=s->chain_minus=0;
}
static void select_pattern(Synth *s,int id){
  publish_bar(s);
  s->edit_pattern=CLAMP(id,0,s->pattern_count-1);
  s->edit_bar=0;
  s->pat=pattern_grid[s->edit_pattern][0];
  s->current=0;
}
static void add_bar(Synth *s){
  int p=s->edit_pattern, n=bar_counts[p];
  if(n>=MAX_BARS)return;
  publish_bar(s);
  pattern_grid[p][n]=pattern_grid[p][n-1];
  bar_counts[p]=n+1;select_bar(s,n);s->current=0;
}
static void delete_bar(Synth *s){
  int p=s->edit_pattern,n=bar_counts[p];
  if(n<=1)return;
  publish_bar(s);
  for(int i=s->edit_bar;i<n-1;i++)pattern_grid[p][i]=pattern_grid[p][i+1];
  bar_counts[p]--;
  s->edit_bar=CLAMP(s->edit_bar,0,bar_counts[p]-1);
  s->pat=pattern_grid[p][s->edit_bar];s->current=0;s->dirty=1;
}
static char data_dir[1024]=".";
static const char *library_message="SAVED";
#define HISTORY 32
static Pattern undo_stack[HISTORY], redo_stack[HISTORY];
static int undo_count=0, redo_count=0, clipboard_valid=0, repeat_edit=0;
static Step clipboard_step;
static void checkpoint(Synth *s){
  if(repeat_edit)return; /* A held direction is one undo operation. */
  if(undo_count==HISTORY){memmove(undo_stack,undo_stack+1,(HISTORY-1)*sizeof(Pattern));undo_count--;}
  undo_stack[undo_count++]=s->pat; redo_count=0; s->dirty=1;
}
/* Create a new variation strictly after the final pattern in the chain.
   Every chain entry owns a distinct bank slot. No overwrites. */
static int chain_add_variation(Synth *s){
  if(s->chain_len>=CHAINS || s->chain_pos!=s->chain_len-1)return 0;
  int used[BANKS]={0};
  for(int i=0;i<s->chain_len;i++)used[CLAMP(s->chain[i],0,BANKS-1)]=1;
  int slot=-1;
  for(int i=0;i<BANKS;i++)if(!used[i]){slot=i;break;}
  if(slot<0)return 0;
  s->bank[s->active]=s->pat;
  s->bank[slot]=s->pat;
  s->chain[s->chain_len++]=slot;
  s->dirty=1;
  s->chain_enabled=1;
  return 1;
}
/* Remove the selected pattern from the chain, never the final remaining one.
   Bank slot data stays in memory until reused; only the chain membership changes. */
static int chain_remove_selected(Synth *s){
  if(s->chain_len<=1)return 0;
  int removed_pos=s->chain_pos;
  s->bank[s->active]=s->pat;
  for(int i=removed_pos;i<s->chain_len-1;i++)s->chain[i]=s->chain[i+1];
  s->chain_len--;
  s->chain_pos=CLAMP(removed_pos,0,s->chain_len-1);
  s->chain_enabled=s->chain_len>1;
  s->active=s->chain[s->chain_pos];
  s->pat=s->bank[s->active];
  /* Playback and edit positions are independent; repair playback index
     without changing the rendered editor page during playback. */
  if(s->play_chain_pos>removed_pos)s->play_chain_pos--;
  else if(s->play_chain_pos==removed_pos)s->play_chain_pos=CLAMP(removed_pos,0,s->chain_len-1);
  s->play_chain_pos=CLAMP(s->play_chain_pos,0,s->chain_len-1);
  s->play_slot=s->chain[s->play_chain_pos];
  s->play_pat=s->bank[s->play_slot];
  s->chain_plus=s->chain_minus=0;
  s->dirty=1;
  return 1;
}
/* Project menu adjusts chain length; growth copies the last pattern,
   reduction deletes from the right, never below one. */
static void chain_resize(Synth *s,int requested){
  requested=CLAMP(requested,1,CHAINS);
  s->bank[s->active]=s->pat; /* Preserve unsaved edits before switching slots. */
  while(s->chain_len<requested){
    int edit_pos=s->chain_pos;
    s->chain_pos=s->chain_len-1;
    s->active=s->chain[s->chain_pos];
    s->pat=s->bank[s->active];
    if(!chain_add_variation(s))break;
    s->chain_pos=edit_pos;
    s->active=s->chain[edit_pos];s->pat=s->bank[s->active];
  }
  while(s->chain_len>requested){
    s->bank[s->active]=s->pat;
    int removing=s->chain_len-1;
    s->chain_len--;
    if(s->chain_pos>=s->chain_len){s->chain_pos=s->chain_len-1;s->active=s->chain[s->chain_pos];s->pat=s->bank[s->active];}
    if(s->play_chain_pos>=s->chain_len)s->play_chain_pos=0;
    (void)removing;
  }
  s->chain_enabled=s->chain_len>1;
  s->chain_plus=s->chain_minus=0;
  s->play_slot=s->chain[s->play_chain_pos];
  s->dirty=1;
}
static void chain_select(Synth *s,int next_pos){
  if(!s->chain_enabled||s->chain_len<2)return;
  next_pos=(next_pos+s->chain_len)%s->chain_len;
  s->bank[s->active]=s->pat;
  s->chain_pos=next_pos; /* editor position only; does not touch playback */
  s->active=s->chain[next_pos];
  s->pat=s->bank[s->active];
  s->current=(next_pos>=0)?s->current:0;
}
static void apply_tool(Synth *s,int id){
  if(id==0){if(undo_count){if(redo_count<HISTORY)redo_stack[redo_count++]=s->pat;s->pat=undo_stack[--undo_count];s->dirty=1;}}
  else if(id==1){if(redo_count){if(undo_count<HISTORY)undo_stack[undo_count++]=s->pat;s->pat=redo_stack[--redo_count];s->dirty=1;}}
  else if(id==2){clipboard_step=s->pat.step[s->current];clipboard_valid=1;}
  else if(id==3){if(clipboard_valid){checkpoint(s);s->pat.step[s->current]=clipboard_step;}}
  else if(id==4){checkpoint(s);Step last=s->pat.step[STEPS-1];for(int i=STEPS-1;i>0;i--)s->pat.step[i]=s->pat.step[i-1];s->pat.step[0]=last;}
  else if(id==5){checkpoint(s);Step first=s->pat.step[0];for(int i=0;i<STEPS-1;i++)s->pat.step[i]=s->pat.step[i+1];s->pat.step[STEPS-1]=first;}
  else if(id==6){return;}
  else if(id==7){checkpoint(s);unsigned int seed=s->noise_seed;for(int i=0;i<STEPS;i++){Step *st=&s->pat.step[i];seed=seed*1664525u+1013904223u;st->on=(seed%5)!=0;seed=seed*1664525u+1013904223u;int n=36+(int)(seed%25);st->note=n;st->accent=(i%4==0);st->slide=(i%8==6);}s->noise_seed=seed;}
}

static const char *notes[] = {"C","C#","D","D#","E","F","F#","G","G#","A","A#","B"};

static double hz(int n) {return 440.0*pow(2.0,(n-69)/12.0);}
static double polyblep(double t, double dt) {
  if(t<dt){t/=dt;return t+t-t*t-1.0;}
  if(t>1.0-dt){t=(t-1.0)/dt;return t*t+t+t+1.0;}
  return 0.0;
}
static void tick(Synth *s) {
  int next=(s->pos+1)%STEPS;
  if(next==0 && s->pos>=0){
    s->play_bar++;
    if(s->play_bar>=bar_counts[s->play_pattern]){
      s->play_bar=0;
      if(s->chain_on && s->chain_size>0){
        s->play_chain_pos=(s->play_chain_pos+1)%s->chain_size;
        s->play_pattern=CLAMP(s->chain_items[s->play_chain_pos],0,s->pattern_count-1);
      }
    }
    s->play_pat=pattern_grid[s->play_pattern][s->play_bar];
    if(s->play_pattern==s->edit_pattern && s->play_bar==s->edit_bar)s->play_pat=s->pat;
  }
  s->pos=next;
  Pattern *p=&s->play_pat;
  Step *st=&p->step[s->pos];
  int prev=(s->pos+STEPS-1)%STEPS;
  int connecting=p->step[prev].on && p->step[prev].slide && s->playing;
  if(st->on){
    s->target=hz(st->note);
    if(!connecting){
      s->freq=s->target;s->amp_stage=1;s->amp_env=0.0;
      s->env=(st->accent?1.25:1.0)*(st->velocity/100.0);
      s->filter_env=st->accent?1.75:1.0;
    }else if(s->amp_stage==4 || s->amp_stage==0)s->amp_stage=3;
    s->playing=1;
  }else if(!connecting){s->playing=0;if(s->amp_stage!=0)s->amp_stage=4;}
}
static void audio_cb(void *userdata, Uint8 *stream, int bytes) {
  Synth *s=userdata;
  float *out=(float*)stream;
  int frames=bytes/(int)(sizeof(float)*2);
  Pattern *p=&s->play_pat;
  for(int i=0;i<frames;i++) {
    if(s->running) {
      if(s->samples_to_step<=0.0){tick(s);s->samples_to_step+=SR*60.0/(s->project_bpm*4.0);}
      s->samples_to_step-=1.0;
    }
    double glide=1.0-exp(-1.0/(SR*(0.005+s->slide_time*0.002)));
    s->freq+=(s->target-s->freq)*glide;
    double inc=CLAMP(s->freq/SR,0.00001,0.40);
    s->phase+=inc;if(s->phase>=1.0)s->phase-=1.0;
    p=&s->play_pat;
    double osc, saw=2.0*s->phase-1.0-polyblep(s->phase,inc);
    double pulse=(s->phase<0.25?1.0:-1.0)+polyblep(s->phase,inc)-polyblep(fmod(s->phase+0.75,1.0),inc);
    switch(p->wave){
      case 0: osc=saw;break;
      case 1: osc=(s->phase<0.5?1.0:-1.0)+polyblep(s->phase,inc)-polyblep(fmod(s->phase+0.5,1.0),inc);break;
      case 2: s->tri+= (s->phase<0.5?1.0:-1.0)*inc*4.0; s->tri=CLAMP(s->tri,-1.0,1.0);osc=s->tri;break;
      case 3: osc=sin(2.0*PI*s->phase);break;
      case 4: osc=pulse;break;
      default: s->noise_seed=s->noise_seed*1664525u+1013904223u;osc=((s->noise_seed>>8)&65535)/32767.5-1.0;break;
    }
    // Real ADSR: sustain is a held level, not a post-filter volume multiplier.
    // Note: gate duration and ADSR release are intentionally independent.
    Step *playing_step=&p->step[CLAMP(s->pos,0,15)];
    double step_len=SR*60.0/(s->project_bpm*4.0);
    if(s->running && s->pos>=0 && s->playing && !playing_step->slide &&
       s->samples_to_step < step_len*(1.0-playing_step->gate/100.0)) {
       s->playing=0; if(s->amp_stage!=0)s->amp_stage=4;
    }
    /* Perceptually predictable 0..100 mapping: bounded and monotonic.
       Time is in seconds, small settings must not create multi-second tails. */
    double at=0.002+1.20*(s->attack/100.0);
    double dt=0.015+2.00*(p->decay/100.0);
    double rt=0.012+2.50*(s->release/100.0);
    double sus=s->sustain/100.0;
    /* Linear-time ADSR stages: duration at 10 means roughly 10% of the range,
       not 6 time constants of an exponential tail. */
    if(s->amp_stage==1){
      s->amp_env+=1.0/(SR*at);
      if(s->amp_env>=1.0){s->amp_env=1.0;s->amp_stage=2;}
    }else if(s->amp_stage==2){
      s->amp_env-=(1.0-sus)/(SR*dt);
      if(s->amp_env<=sus){s->amp_env=sus;s->amp_stage=3;}
    }else if(s->amp_stage==3){s->amp_env=sus;}
    else if(s->amp_stage==4){
      s->amp_env-=1.0/(SR*rt);
      if(s->amp_env<=0.0){s->amp_env=0.0;s->amp_stage=0;}
    }
    // Dedicated filter envelope, longer ranges for aggressive sweeps.
    double filter_decay=0.015+2.00*(p->decay/100.0);
    s->filter_env*=exp(-1.0/(SR*filter_decay));
    s->lfo_phase+=(0.05+s->mod_rate*0.15)/SR;
    if(s->lfo_phase>=1.0)s->lfo_phase-=1.0;
    double cv=(playing_step->cutoff_lock>=0?playing_step->cutoff_lock:p->cutoff)/100.0;
    double lfo=sin(2.0*PI*s->lfo_phase);
    // CUTOFF follows a logarithmic Hz scale, FILTER ENV changes cutoff in octaves.
    double cutoff_base=38.0*pow(390.0,cv);
    double env_octaves=5.0*(p->envmod/100.0)*s->filter_env;
    double fm_octaves=2.0*(s->filter_fm/100.0)*lfo;
    double f=CLAMP(cutoff_base*pow(2.0,env_octaves+fm_octaves),30.0,14500.0);
    double a=1.0-exp(-2.0*PI*f/SR);
    double accent=playing_step->accent?1.25:1.0;
    // Input saturation before filtering. ACID: four resonant poles, SMOOTH: two.
    double pregain=1.0+7.0*(p->drive/100.0);
    double input=tanh(osc*pregain)*accent;
    double resonance=p->resonance/100.0;
    double filtered;
    if(s->filter_mode==0){
      double fb=3.2*resonance;
      double u=tanh(input-fb*s->lp4);
      s->lp1+=a*(u-s->lp1);
      s->lp2+=a*(tanh(s->lp1)-s->lp2);
      s->lp3+=a*(tanh(s->lp2)-s->lp3);
      s->lp4+=a*(tanh(s->lp3)-s->lp4);
      filtered=s->lp4*1.55;
    }else{
      double u=tanh(input-1.2*resonance*s->lp2);
      s->lp1+=a*(u-s->lp1);
      s->lp2+=a*(s->lp1-s->lp2);
      filtered=s->lp2;
      s->lp3*=0.999;s->lp4*=0.999;
    }
    double level=CLAMP(s->amp_env,0.0,1.0)*(playing_step->velocity/100.0);
    // Final soft limiter for headphones and strong resonance settings.
    double sig=tanh(filtered*level*0.85)*0.48;
    sig*=1.0+0.14*(s->mod_depth/100.0)*lfo;
    if(!s->running) sig=0.0; /* STOP is absolute silence, not an infinite ADSR hold. */
    out[2*i]=out[2*i+1]=(float)sig;
  }
  s->frame+=(uint64_t)frames;
}
static void defaults(Pattern *p){
  memset(p,0,sizeof(*p));p->bpm=128;p->cutoff=49;p->resonance=65;p->decay=35;p->envmod=50;p->drive=24;p->wave=0;
  int pitch[16]={36,36,39,43,36,48,39,36,41,39,36,43,48,43,39,36};
  for(int i=0;i<16;i++) {p->step[i].velocity=100;p->step[i].gate=100;p->step[i].cutoff_lock=-1;p->step[i].note=pitch[i];p->step[i].on=(i%4!=1);p->step[i].accent=(i==3||i==8||i==12);p->step[i].slide=(i==4||i==11);}
}
static void sanitize(Pattern *q);
static int write_atomic(const char *name,const char *text){
  char temp[1100];snprintf(temp,sizeof(temp),"%s.tmp",name);
  FILE *f=fopen(temp,"w");if(!f)return 0;
  int written=fputs(text,f);int closed=fclose(f);if(written<0 || closed!=0){remove(temp);return 0;}
  if(rename(temp,name)!=0){remove(temp);return 0;}return 1;
}
/* Each category has 32 independent user slots. Factory presets are never deleted. */
#define LIB_SLOTS 32
static const char *library_folder(int type){return type==0?"projects":type==1?"sounds":"sequences";}
static const char *library_filename(int type){return type==0?"session-v08.bin":type==1?"sound_preset.txt":"sequence_preset.txt";}
static void library_dir(char *out,size_t n,const char *root,int type,int slot){
 snprintf(out,n,"%s/library/%s/slot%02d",root,library_folder(type),slot+1);
}
static int mkdir_safe(const char *p){return mkdir(p,0755)==0 || errno==EEXIST;}
static int library_prepare(const char *root,int type,int slot){
 char p[1024];snprintf(p,sizeof(p),"%s/library",root);if(!mkdir_safe(p))return 0;
 snprintf(p,sizeof(p),"%s/library/%s",root,library_folder(type));if(!mkdir_safe(p))return 0;
 library_dir(p,sizeof(p),root,type,slot);return mkdir_safe(p);
}
static int library_exists(const char *root,int type,int slot){
 char d[1024],p[1200];library_dir(d,sizeof(d),root,type,slot);
 snprintf(p,sizeof(p),"%s/%s",d,library_filename(type));FILE *f=fopen(p,"r");if(!f)return 0;fclose(f);return 1;
}
static int library_delete(const char *root,int type,int slot){
 char d[1024],p[1200];library_dir(d,sizeof(d),root,type,slot);
 if(!library_exists(root,type,slot))return 0;
 snprintf(p,sizeof(p),"%s/%s",d,library_filename(type));if(remove(p)!=0)return 0;
 if(type==0){snprintf(p,sizeof(p),"%s/project.txt",d);remove(p);}
 return 1;
}
static void project_path(char *out,size_t n,const char *dir){snprintf(out,n,"%s/project.txt",dir);}
static void sound_path(char *out,size_t n,const char *dir){snprintf(out,n,"%s/sound_preset.txt",dir);}
static void sequence_path(char *out,size_t n,const char *dir){snprintf(out,n,"%s/sequence_preset.txt",dir);}
static int save_project(Synth *s,const char *dir){
 char path[1024],buf[256];project_path(path,sizeof(path),dir);
 snprintf(buf,sizeof(buf),"SXPROJECT61 %d %d %d %d %d %d %d %d\n",s->project_bpm,s->attack,s->sustain,s->release,s->filter_fm,s->slide_time,s->mod_rate,s->filter_mode);
 return write_atomic(path,buf);
}
static void load_project(Synth *s,const char *dir){
 char path[1024],sig[32];project_path(path,sizeof(path),dir);FILE *f=fopen(path,"r");if(!f)return;
 int bpm=128,a=0,sus=85,r=12,fm=0,slide=12,rate=20,lock=0,root=0,scale=0;
 int got=fscanf(f,"%31s %d %d %d %d %d %d %d %d %d %d",sig,&bpm,&a,&sus,&r,&fm,&slide,&rate,&lock,&root,&scale);
 if((strcmp(sig,"SXPROJECT61")==0 && got>=9)||(strcmp(sig,"SXPROJECT6")==0 && got==11)||(strcmp(sig,"ACIDPROJECT4")==0 && got>=8)){
 s->project_bpm=CLAMP(bpm,40,240);s->attack=CLAMP(a,0,100);s->sustain=CLAMP(sus,0,100);s->release=CLAMP(r,0,100);s->filter_fm=CLAMP(fm,0,100);s->slide_time=CLAMP(slide,0,100);s->mod_rate=CLAMP(rate,0,100);
 if(strcmp(sig,"SXPROJECT61")==0)s->filter_mode=CLAMP(lock,0,1); /* Legacy scale settings intentionally ignored. */
 }fclose(f);
}
static void sound_preset(Synth *s,int i){
 // 8 bundled timbres, selectable without touching the note sequence.
 const int presets[8][9]={
 {0,48,75,52,65,24,18,38,16}, // Acid Classic
 {1,30,88,22,82,70,0,18,45}, // Rubber
 {2,68,40,78,35,10,50,45,25}, // Soft Triangle
 {3,22,85,90,68,32,75,90,6}, // Resonant Drone
 {4,53,60,30,70,65,4,34,68}, // Pulse Bite
 {5,62,30,42,65,85,0,14,87}, // Noise Hit
 {0,80,80,23,90,90,0,22,92}, // Razor
 {3,44,33,95,15,15,85,80,30}  // Floating
 };
 i=CLAMP(i,0,7);Pattern *p=&s->pat;
 p->wave=presets[i][0];p->cutoff=presets[i][1];p->resonance=presets[i][2];p->decay=presets[i][3];p->envmod=presets[i][4];p->drive=presets[i][5];
 s->attack=presets[i][6];s->release=presets[i][7];s->filter_fm=presets[i][8];
}
static int save_sound(Synth *s,const char *dir){
 char path[1024],buf[256];sound_path(path,sizeof(path),dir);
 snprintf(buf,sizeof(buf),"ACIDSOUND4 %d %d %d %d %d %d %d %d %d %d %d %d %d\n",s->pat.wave,s->pat.cutoff,s->pat.resonance,s->pat.decay,s->pat.envmod,s->pat.drive,s->attack,s->sustain,s->release,s->filter_fm,s->slide_time,s->mod_depth,s->mod_rate);
 return write_atomic(path,buf);
}
static int load_sound(Synth *s,const char *dir){
 char path[1024],sig[32];sound_path(path,sizeof(path),dir);FILE *f=fopen(path,"r");if(!f)return 0;
 int v[13],ok=fscanf(f,"%31s",sig)==1 && strcmp(sig,"ACIDSOUND4")==0;
 for(int i=0;i<13&&ok;i++)ok=fscanf(f,"%d",&v[i])==1;
 fclose(f);if(!ok)return 0;
 s->pat.wave=CLAMP(v[0],0,5);s->pat.cutoff=CLAMP(v[1],0,100);s->pat.resonance=CLAMP(v[2],0,95);s->pat.decay=CLAMP(v[3],0,100);s->pat.envmod=CLAMP(v[4],0,100);s->pat.drive=CLAMP(v[5],0,100);
 s->attack=CLAMP(v[6],0,100);s->sustain=CLAMP(v[7],0,100);s->release=CLAMP(v[8],0,100);s->filter_fm=CLAMP(v[9],0,100);s->slide_time=CLAMP(v[10],0,100);s->mod_depth=CLAMP(v[11],0,100);s->mod_rate=CLAMP(v[12],0,100);return 1;
}
/* Eight ORIGINAL acid-style patterns inspired by early 303 sequencing methods.
   They are not transcriptions of copyrighted Roland factory patterns. */
static void seq_preset(Synth *s,int i){
 static const int pitches[8][16]={
  {36,36,39,43,36,48,39,36,41,39,36,43,48,43,39,36},
  {36,43,36,46,39,36,48,43,36,41,43,39,36,46,48,36},
  {36,36,48,36,43,39,36,46,48,36,41,39,36,43,36,48},
  {41,41,48,41,44,41,51,48,41,53,48,44,41,48,44,41},
  {36,39,43,46,48,46,43,39,36,39,46,43,48,46,39,36},
  {33,45,33,40,36,45,40,33,45,40,33,36,45,43,40,33},
  {38,41,45,50,38,48,45,41,38,50,45,41,53,48,45,38},
  {36,37,42,37,44,42,37,47,36,37,42,49,44,42,37,36}
 };
 static const char *mask[8]={"1110111011101110","1011110110111101","1111011111101101","1101101110111101","1111111111111111","1010101110101110","1110111101110111","1111110111111101"};
 static const char *accent[8]={"0010001010001000","1000100010001000","1001000010010010","1000101000010100","1000100010001000","1010100010100010","1001000100100100","1000010000100100"};
 static const char *slide[8]={"0001000100010000","0010000100010000","0000100010001000","0010001000100010","0101010101010100","0001000001001000","0010001000010010","0100010001000100"};
 i=CLAMP(i,0,7);
 for(int j=0;j<STEPS;j++){
   Step *st=&s->pat.step[j];
   st->note=pitches[i][j];st->on=mask[i][j]=='1';
   st->accent=accent[i][j]=='1';st->slide=slide[i][j]=='1';
   st->gate=(j%4==0)?92:((j%3==0)?74:60);
   st->velocity=st->accent?118:95;st->cutoff_lock=-1;
 }
}
static int save_sequence(Synth *s,const char *dir){
 char path[1024],tmp[1100];sequence_path(path,sizeof(path),dir);snprintf(tmp,sizeof(tmp),"%s.tmp",path);
 FILE *f=fopen(tmp,"w");if(!f)return 0;fprintf(f,"ACIDSEQ4\n");
 for(int i=0;i<STEPS;i++){Step *st=&s->pat.step[i];fprintf(f,"%d %d %d %d %d %d %d\n",st->note,st->on,st->accent,st->slide,st->velocity,st->gate,st->cutoff_lock);}
 if(fclose(f)!=0){remove(tmp);return 0;}if(rename(tmp,path)!=0){remove(tmp);return 0;}return 1;
}
static int load_sequence(Synth *s,const char *dir){
 char path[1024],sig[32];sequence_path(path,sizeof(path),dir);FILE *f=fopen(path,"r");if(!f)return 0;
 Step steps[STEPS];int ok=fscanf(f,"%31s",sig)==1 && strcmp(sig,"ACIDSEQ4")==0;
 for(int i=0;i<STEPS&&ok;i++){Step *st=&steps[i];ok=fscanf(f,"%d %d %d %d %d %d %d",&st->note,&st->on,&st->accent,&st->slide,&st->velocity,&st->gate,&st->cutoff_lock)==7;}fclose(f);if(!ok)return 0;
 memcpy(s->pat.step,steps,sizeof(steps));sanitize(&s->pat);return 1;
}
static void path_for(char *out,size_t n,const char *arg){snprintf(out,n,"%s/bank.txt",arg);}
static void legacy_path(char *out,size_t n,const char *arg){snprintf(out,n,"%s/pattern.txt",arg);}
/* v0.8 saves have their own signature and are never read as old banks. */
typedef struct {char sig[12];uint32_t version,pattern_count,edit_pattern,edit_bar,chain_size,chain_on;
  uint32_t reserved;} DiskHeader;
static int save(Synth *s,const char *dir){
  publish_bar(s);
  char path[1100],temp[1140];snprintf(path,sizeof(path),"%s/session-v08.bin",dir);snprintf(temp,sizeof(temp),"%s.tmp",path);
  FILE *fp=fopen(temp,"wb");if(!fp)return 0;
  DiskHeader h={{0},8,(uint32_t)s->pattern_count,(uint32_t)s->edit_pattern,(uint32_t)s->edit_bar,
    (uint32_t)s->chain_size,(uint32_t)s->chain_on,0};memcpy(h.sig,"ANTRESOLI08",11);
  int ok=fwrite(&h,sizeof(h),1,fp)==1;
  ok &= fwrite(&s->project_bpm,sizeof(int),1,fp)==1;
  int dsp[]={s->attack,s->sustain,s->release,s->filter_fm,s->slide_time,s->mod_rate,s->mod_depth,s->filter_mode};
  ok &= fwrite(dsp,sizeof(dsp),1,fp)==1;
  ok &= fwrite(s->chain_items,sizeof(int),CHAINS,fp)==CHAINS;
  for(int p=0;p<s->pattern_count && ok;p++){
    ok &= fwrite(&bar_counts[p],sizeof(int),1,fp)==1;
    ok &= fwrite(pattern_grid[p],sizeof(Pattern),bar_counts[p],fp)==(size_t)bar_counts[p];
  }
  if(fclose(fp)!=0)ok=0;
  if(!ok){remove(temp);return 0;}
  if(rename(temp,path)!=0){remove(temp);return 0;}return 1;
}
static void sanitize(Pattern *q){
  q->bpm=CLAMP(q->bpm,40,240);q->cutoff=CLAMP(q->cutoff,0,100);q->resonance=CLAMP(q->resonance,0,95);
  q->decay=CLAMP(q->decay,0,100);q->envmod=CLAMP(q->envmod,0,100);q->drive=CLAMP(q->drive,0,100);q->wave=CLAMP(q->wave,0,5);
  for(int i=0;i<STEPS;i++){q->step[i].note=CLAMP(q->step[i].note,24,84);q->step[i].on=!!q->step[i].on;q->step[i].accent=!!q->step[i].accent;q->step[i].slide=!!q->step[i].slide;q->step[i].velocity=CLAMP(q->step[i].velocity,1,127);q->step[i].gate=CLAMP(q->step[i].gate,1,100);q->step[i].cutoff_lock=CLAMP(q->step[i].cutoff_lock,-1,100);}
}
static int read_pattern(FILE *f,Pattern *q,int version){
  if(fscanf(f,"%d %d %d %d %d %d %d",&q->bpm,&q->cutoff,&q->resonance,&q->decay,&q->envmod,&q->drive,&q->wave)!=7)return 0;
  for(int i=0;i<STEPS;i++){
    Step *st=&q->step[i];st->velocity=100;st->gate=100;st->cutoff_lock=-1;
    if(fscanf(f,"%d %d %d %d",&st->note,&st->on,&st->accent,&st->slide)!=4)return 0;
    if(version>=3 && fscanf(f,"%d %d %d",&st->velocity,&st->gate,&st->cutoff_lock)!=3)return 0;
  }
  sanitize(q);return 1;
}
static int load(Synth *s,const char *dir){
  char path[1100];snprintf(path,sizeof(path),"%s/session-v08.bin",dir);FILE *fp=fopen(path,"rb");if(!fp)return 0;
  DiskHeader h;int ok=fread(&h,sizeof(h),1,fp)==1;
  if(!ok||memcmp(h.sig,"ANTRESOLI08",11)||h.version!=8||h.pattern_count<1||h.pattern_count>MAX_PATTERNS
     ||h.chain_size>CHAINS||h.edit_pattern>=h.pattern_count){fclose(fp);return 0;}
  int bpm,dsp[8],items[CHAINS],counts[MAX_PATTERNS];
  Pattern *tmp=malloc(sizeof(pattern_grid));if(!tmp){fclose(fp);return 0;}
  ok=fread(&bpm,sizeof(int),1,fp)==1;
  ok &= fread(dsp,sizeof(dsp),1,fp)==1;
  ok &= fread(items,sizeof(int),CHAINS,fp)==CHAINS;
  for(unsigned p=0;p<h.pattern_count && ok;p++){
    ok &= fread(&counts[p],sizeof(int),1,fp)==1;
    if(!ok||counts[p]<1||counts[p]>MAX_BARS){ok=0;break;}
    ok &= fread(tmp+p*MAX_BARS,sizeof(Pattern),counts[p],fp)==(size_t)counts[p];
  }
  fclose(fp);
  for(unsigned i=0;i<h.chain_size;i++)if(items[i]<0||items[i]>=(int)h.pattern_count)ok=0;
  if(ok){
    memcpy(pattern_grid,tmp,sizeof(pattern_grid));
    memcpy(bar_counts,counts,h.pattern_count*sizeof(int));
    memcpy(s->chain_items,items,sizeof(items));
    s->pattern_count=h.pattern_count;s->edit_pattern=h.edit_pattern;
    s->edit_bar=CLAMP((int)h.edit_bar,0,bar_counts[s->edit_pattern]-1);
    s->chain_size=h.chain_size;s->chain_on=h.chain_on && h.chain_size>0;
    s->project_bpm=CLAMP(bpm,40,240);
    s->attack=CLAMP(dsp[0],0,100);s->sustain=CLAMP(dsp[1],0,100);s->release=CLAMP(dsp[2],0,100);
    s->filter_fm=CLAMP(dsp[3],0,100);s->slide_time=CLAMP(dsp[4],0,100);
    s->mod_rate=CLAMP(dsp[5],0,100);s->mod_depth=CLAMP(dsp[6],0,100);s->filter_mode=CLAMP(dsp[7],0,1);
    s->pat=pattern_grid[s->edit_pattern][s->edit_bar];s->play_pattern=s->edit_pattern;s->play_bar=0;
    s->play_chain_pos=0;s->play_pat=pattern_grid[s->play_pattern][0];s->pos=-1;s->running=0;s->dirty=0;
  }
  free(tmp);return ok;
}
static int library_save(Synth *s,const char *root,int type,int slot){
 char d[1024];if(!library_prepare(root,type,slot))return 0;
 library_dir(d,sizeof(d),root,type,slot);
 if(type==0)return save(s,d);
 if(type==1)return save_sound(s,d);
 return save_sequence(s,d);
}
static int library_load(Synth *s,const char *root,int type,int slot){
 if(!library_exists(root,type,slot))return 0;
 char d[1024];library_dir(d,sizeof(d),root,type,slot);
 if(type==0){
   if(!load(s,d))return 0;
   /* The v0.8 session file includes global project parameters. */
   s->play_chain_pos=0;s->play_pattern=s->edit_pattern;s->play_bar=0;s->play_pat=pattern_grid[s->play_pattern][0];
   s->running=0;s->playing=0;s->amp_stage=0;s->amp_env=0.0;
   s->filter_env=s->lp1=s->lp2=s->lp3=s->lp4=0.0;
   s->pos=-1;s->samples_to_step=0.0;s->step_edit=0;s->chain_plus=s->chain_minus=0;
   undo_count=redo_count=0;s->dirty=1;return 1;
 }
 int ok=type==1?load_sound(s,d):load_sequence(s,d);
 if(ok){s->bank[s->active]=s->pat;s->dirty=1;undo_count=redo_count=0;}
 return ok;
}
// Tiny 3x5 pixel glyphs. Text is intentionally legible at 640x480 without fonts.
static const char *glyph(char c){
  switch(c){
    case 'A':return "010101111101101";case 'B':return "110101110101110";case 'C':return "011100100100011";
    case 'D':return "110101101101110";case 'E':return "111100110100111";case 'F':return "111100110100100";
    case 'G':return "011100101101011";case 'H':return "101101111101101";case 'I':return "111010010010111";
    case 'J':return "001001001101010";case 'K':return "101101110101101";case 'L':return "100100100100111";
    case 'M':return "101111111101101";case 'N':return "101111111111101";case 'O':return "010101101101010";
    case 'P':return "110101110100100";case 'Q':return "010101101111011";case 'R':return "110101110101101";
    case 'S':return "011100010001110";case 'T':return "111010010010010";case 'U':return "101101101101111";
    case 'V':return "101101101101010";case 'W':return "101101111111101";case 'X':return "101101010101101";
    case 'Y':return "101101010010010";case 'Z':return "111001010100111";
    case '0':return "111101101101111";case '1':return "010110010010111";case '2':return "110001111100111";
    case '3':return "110001111001110";case '4':return "101101111001001";case '5':return "111100110001110";
    case '6':return "011100110101010";case '7':return "111001010010010";case '8':return "010101010101010";
    case '9':return "010101011001110";case '#':return "101111101111101";case '-':return "000000111000000";
    case ':':return "000010000010000";case '/':return "001001010100100";case '.':return "000000000000010";
    case '+':return "000010111010000";case '%':return "101001010100101";
    default:return "000000000000000";
  }
}
static void rect(SDL_Renderer *r,int x,int y,int w,int h,SDL_Color c){SDL_SetRenderDrawColor(r,c.r,c.g,c.b,255);SDL_Rect q={x,y,w,h};SDL_RenderFillRect(r,&q);}
static void txt(SDL_Renderer *r,int x,int y,int scale,const char *s,SDL_Color c){
  for(;*s;s++,x+=scale*4){const char *g=glyph(*s);for(int k=0;k<15;k++)if(g[k]=='1')rect(r,x+(k%3)*scale,y+(k/3)*scale,scale,scale,c);}
}
static void bar(SDL_Renderer *r,int x,int y,int val,int max,SDL_Color green,SDL_Color dim){
  rect(r,x,y,310,9,dim);rect(r,x,y,310*CLAMP(val,0,max)/max,9,green);
}
static void render(SDL_Renderer *r,Synth *s,int field,int msg){
 const SDL_Color bg={13,23,21,255},white={211,241,209,255},green={95,216,136,255},dim={81,110,94,255},orange={255,183,89,255},blue={98,158,233,255};
 char tmp[128];rect(r,0,0,640,480,bg);
 txt(r,20,12,4,"ANTRESOLI SX",green);
 if(s->dirty)txt(r,282,12,3,"*",orange);
 snprintf(tmp,sizeof(tmp),"P%02d  %d BPM",s->edit_pattern+1,s->project_bpm);txt(r,410,15,3,tmp,white);
 const char *tabs[]={"SEQ","ADSR","FX"};
 for(int i=0;i<3;i++){int x=18+i*208;rect(r,x,49,199,38,i==s->page?(SDL_Color){76,155,95,255}:(SDL_Color){29,55,40,255});txt(r,x+40,60,3,tabs[i],i==s->page?bg:white);}
 if(s->page==0){
  for(int i=0;i<16;i++){
   int x=20+(i%8)*76,y=108+(i/8)*86;Step *st=&s->pat.step[i];
   rect(r,x,y,70,78,st->on?(SDL_Color){38,77,50,255}:(SDL_Color){23,42,32,255});
   if(i==s->current){rect(r,x,y,70,3,green);rect(r,x,y,3,78,green);rect(r,x+67,y,3,78,green);rect(r,x,y+75,70,3,green);}
   if(s->running&&s->pos==i)rect(r,x+6,y+5,7,7,orange);
   snprintf(tmp,sizeof(tmp),"%02d",i+1);txt(r,x+25,y+12,2,tmp,dim);
   if(st->on){snprintf(tmp,sizeof(tmp),"%s%d",notes[st->note%12],st->note/12-1);txt(r,x+9,y+37,3,tmp,white);}else txt(r,x+29,y+37,3,"-",dim);
   if(st->accent)txt(r,x+7,y+64,2,"A",orange);
   if(st->slide)txt(r,x+49,y+64,2,"S",blue);
  }
  if(s->step_edit){Step *st=&s->pat.step[s->current];const char *names[]={"NOTE","VELOCITY","GATE","ACCENT","SLIDE","CUTOFF LOCK"};
   snprintf(tmp,sizeof(tmp),"STEP %02d  %s",s->current+1,names[s->step_field]);txt(r,25,302,4,tmp,green);
   int v[]={st->note,st->velocity,st->gate,st->accent,st->slide,st->cutoff_lock};
   if(s->step_field==0)snprintf(tmp,sizeof(tmp),"%s%d",notes[st->note%12],st->note/12-1);
   else if(s->step_field==5&&v[5]<0)snprintf(tmp,sizeof(tmp),"OFF");else snprintf(tmp,sizeof(tmp),"%d",v[s->step_field]);
   txt(r,28,346,5,tmp,white);txt(r,24,409,2,"L/R FIELD  LEFT/RIGHT 1  UP/DOWN 10  B BACK",dim);
  }else{
   /* SEQ shows only relevant navigation; all sound control lives in ADSR/FX. */
   txt(r,24,314,3,"X COPY  Y PASTE  A EDIT",white);
   txt(r,24,350,2,"FILTER AND MODULATION: L1/R1 TO FX",dim);
   if(s->chain_plus){
     rect(r,542,280,72,72,(SDL_Color){35,85,51,255});
     txt(r,560,292,6,"+",green);
     txt(r,548,335,2,"A ADD",white);
   }
   if(s->chain_minus){
     rect(r,20,280,86,72,(SDL_Color){92,49,41,255});
     txt(r,47,292,6,"-",orange);
     txt(r,28,335,2,"A DEL",white);
   }
   snprintf(tmp,sizeof(tmp),"PATTERN %d/%d   BAR %d/%d   PLAYLIST: %s",s->edit_pattern+1,s->pattern_count,s->edit_bar+1,bar_counts[s->edit_pattern],s->chain_on?"ON":"OFF");txt(r,24,414,2,tmp,green);
   /* Beat lamp uses audio callback position; it never drives the edited page. */
   {int beat=CLAMP(s->pos,0,15)/4;int lit=s->running && s->pos>=0 && (s->frame%(uint64_t)(SR*60.0/s->project_bpm)) < (uint64_t)(SR*0.10);
    SDL_Rect lamp={598,22,17,17};SDL_SetRenderDrawColor(r,lit?145:34,lit?255:71,lit?155:44,255);SDL_RenderFillRect(r,&lamp);
    snprintf(tmp,sizeof(tmp),"%d",beat+1);txt(r,575,22,1,tmp,green);
   }
   }
 }else if(s->page==1 || s->page==2){
   const char *adnm[]={"ATTACK","DECAY","SUSTAIN","RELEASE"};
   const char *fxnm[]={"CUTOFF","RESONANCE","ENV MOD","FILTER FM","DRIVE","SLIDE TIME","LFO RATE","LFO DEPTH","FILTER MODE"};
   int ad[]={s->attack,s->pat.decay,s->sustain,s->release};
   int fx[]={s->pat.cutoff,s->pat.resonance,s->pat.envmod,s->filter_fm,s->pat.drive,s->slide_time,s->mod_rate,s->mod_depth,s->filter_mode};
   int pg=s->page==1, count=pg?4:9,selected=pg?CLAMP(field,0,3):CLAMP(field,0,8),start=pg?0:(selected>=5?4:0),visible=pg?4:5;
   for(int n=0;n<visible;n++){int j=start+n;if(j>=count)break;int y=108+n*56, v=pg?ad[j]:fx[j],max=(!pg&&j==8)?1:100;
    if(j==selected)rect(r,19,y-6,601,48,(SDL_Color){35,75,49,255});
    txt(r,30,y,3,pg?adnm[j]:fxnm[j],j==selected?green:white);
    if(!pg && j==8)snprintf(tmp,sizeof(tmp),"%s",v?"SMOOTH":"ACID");else snprintf(tmp,sizeof(tmp),"%d",v);txt(r,505,y,3,tmp,white);
    bar(r,30,y+27,v,max,green,dim);
   }
   txt(r,24,414,2,"UP/DOWN SELECT  LEFT/RIGHT 1  L2/R2 10",dim);
 }else{
   const char *nm[]={"GLOBAL BPM","EDIT PATTERN","SAVE PROJECT","NEW PATTERN"};
   for(int i=0;i<4;i++){int y=106+i*52;
    if(i==s->project_field)rect(r,20,y-7,595,43,(SDL_Color){35,75,49,255});
    txt(r,30,y,3,nm[i],i==s->project_field?green:white);
    if(i==0)snprintf(tmp,sizeof(tmp),"%d",s->project_bpm);
    if(i==1)snprintf(tmp,sizeof(tmp),"%d/%d",s->edit_pattern+1,s->pattern_count);
    if(i==2)snprintf(tmp,sizeof(tmp),"A SAVE");
    if(i==3)snprintf(tmp,sizeof(tmp),"A CREATE");
    txt(r,440,y,3,tmp,orange);
   }
   txt(r,24,414,2,"GLOBAL SETTINGS  UP/DOWN SELECT  LEFT/RIGHT CHANGE",dim);
 }
 if(s->menu){
  rect(r,12,92,615,350,bg);
  const char *entries[]={"PROJECT","PROJECT FILES","SOUND FILES","SEQUENCE FILES","SOUND PRESETS","SEQUENCE PRESETS","OSCILLATOR","TOOLS","SAVE PROJECT","PATTERN CHAINS","INIT"};
  const char *presets[]={"ACID CLASSIC","RUBBER","SOFT TRIANGLE","RESONANT DRONE","PULSE BITE","NOISE HIT","RAZOR","FLOATING"};
  if(s->menu==5){
    txt(r,24,102,4,"PROJECT SETTINGS",green);
    const char *pn[]={"GLOBAL BPM","EDIT PATTERN","SAVE PROJECT","NEW PATTERN"};
    for(int i=0;i<4;i++){int y=139+i*54; if(i==s->project_field)rect(r,20,y-6,590,48,(SDL_Color){35,75,49,255});
      txt(r,30,y,3,pn[i],i==s->project_field?green:white);
      if(i==0)snprintf(tmp,sizeof(tmp),"%d",s->project_bpm);
      if(i==1)snprintf(tmp,sizeof(tmp),"%d/%d",s->edit_pattern+1,s->pattern_count);
      if(i==2)snprintf(tmp,sizeof(tmp),"A SAVE");
      if(i==3)snprintf(tmp,sizeof(tmp),"A CREATE");
      txt(r,525,y,3,tmp,orange);
    }
  }else if(s->menu==9){
    txt(r,24,102,4,"PATTERN CHAINS",green);
    snprintf(tmp,sizeof(tmp),"%s   %d/128 BLOCKS",s->chain_on?"PLAYLIST ON":"PLAYLIST OFF",s->chain_size);txt(r,24,139,2,tmp,white);
    int first=s->playlist_cursor/7*7;
    for(int j=0;j<7 && first+j<=s->chain_size;j++){
      int k=first+j,y=172+j*35;
      if(k==s->playlist_cursor)rect(r,20,y-2,582,31,(SDL_Color){35,75,49,255});
      if(k==s->chain_size)snprintf(tmp,sizeof(tmp),"%03d  + ADD BLOCK",k+1);
      else snprintf(tmp,sizeof(tmp),"%03d  PATTERN %02d",k+1,s->chain_items[k]+1);
      txt(r,32,y+4,3,tmp,k==s->playlist_cursor?green:white);
    }
    txt(r,24,421,2,"A INSERT  Y REMOVE  X TOGGLE  LEFT/RIGHT PATTERN",dim);
  }else if(s->menu==10){
    txt(r,30,155,4,"INIT NEW PROJECT?",orange);
    txt(r,30,225,3,"RESET UNSAVED SESSION",white);
    txt(r,30,285,2,"A CONFIRM    B CANCEL",dim);
  }else if(s->menu==7){
    const char *kinds[]={"PROJECT FILES","SOUND FILES","SEQUENCE FILES"};
    txt(r,24,102,4,kinds[CLAMP(s->library_type,0,2)],green);
    txt(r,24,138,2,"A LOAD    X SAVE    Y DELETE",dim);
    int first=(s->library_slot/7)*7;
    for(int i=0;i<7 && first+i<LIB_SLOTS;i++){
      int slot=first+i,y=172+i*34;
      if(slot==s->library_slot)rect(r,20,y-3,584,33,(SDL_Color){35,75,49,255});
      snprintf(tmp,sizeof(tmp),"SLOT %02d     %s",slot+1,library_exists(data_dir,s->library_type,slot)?"SAVED":"EMPTY");
      txt(r,31,y+5,3,tmp,slot==s->library_slot?green:white);
    }
    txt(r,24,424,2,"UP/DOWN SELECT   LEFT/RIGHT PAGE   B BACK",dim);
  }else if(s->menu==8){
    rect(r,44,177,550,140,(SDL_Color){43,24,24,255});
    txt(r,67,192,4,"DELETE SAVED SLOT?",orange);
    snprintf(tmp,sizeof(tmp),"SLOT %02d",s->library_slot+1);txt(r,67,239,3,tmp,white);
    txt(r,67,282,2,"A CONFIRM    B CANCEL",dim);
  }else if(s->menu==2){const char *tools[]={"UNDO","REDO","COPY STEP","PASTE STEP","ROTATE RIGHT","ROTATE LEFT","GENERATE PATTERN"};
   for(int i=0;i<7;i++){int y=109+i*38;if(i==s->tool_cursor)rect(r,20,y,590,35,(SDL_Color){35,75,49,255});txt(r,29,y+11,3,tools[i],i==s->tool_cursor?green:white);}
  }else if(s->menu==6){
    const char *wn[]={"SAW","SQUARE","TRIANGLE","SINE","PULSE","NOISE"};
    txt(r,24,112,4,"OSCILLATOR",green);
    txt(r,30,190,3,"WAVE",white);
    txt(r,270,190,4,wn[CLAMP(s->pat.wave,0,5)],green);
    txt(r,30,258,3,"LEFT/RIGHT CHANGE",dim);
    txt(r,30,302,3,"B BACK",dim);
  }  else if(s->menu==3 || s->menu==4){
    txt(r,24,102,4,s->menu==3?"SOUND LIBRARY":"SEQUENCE LIBRARY",green);
    for(int i=0;i<8;i++){int y=139+i*35,selected=s->menu==3?s->preset_cursor:s->seq_cursor;
      if(i==selected)rect(r,21,y-3,585,31,(SDL_Color){35,75,49,255});
      if(s->menu==3)snprintf(tmp,sizeof(tmp),"%02d  %s",i+1,presets[i]);else snprintf(tmp,sizeof(tmp),"%02d  SEQUENCE %02d",i+1,i+1);
      txt(r,30,y+4,3,tmp,i==selected?green:white);
    }
  }else{
   for(int i=0;i<11;i++){int y=107+i*29;if(i==s->menu_cursor)rect(r,20,y,590,35,(SDL_Color){35,75,49,255});txt(r,30,y+7,2,entries[i],i==s->menu_cursor?green:white);}
  }
 }
 rect(r,0,451,640,29,(SDL_Color){18,34,26,255});
 txt(r,22,460,2,s->menu?"A OPEN/LOAD  B BACK  SELECT CLOSE":"L1/R1 TABS  START PLAY  SELECT MENU",dim);
 if(msg)txt(r,524,460,2,library_message,green);
 SDL_RenderPresent(r);
}
static int normkey(SDL_Keycode k){
  switch(k){case SDLK_LEFT:return 1;case SDLK_RIGHT:return 2;case SDLK_UP:return 3;case SDLK_DOWN:return 4;
  case SDLK_z:case SDLK_a:return 5;case SDLK_x:case SDLK_b:return 6;case SDLK_s:return 7;case SDLK_d:case SDLK_y:return 8;
  case SDLK_q:case SDLK_PAGEUP:return 9;case SDLK_w:case SDLK_PAGEDOWN:return 10;
  case SDLK_1:return 15;case SDLK_2:return 16;case SDLK_RETURN:return 11;case SDLK_BACKSPACE:case SDLK_SPACE:return 12;case SDLK_ESCAPE:case SDLK_HOME:case SDLK_MENU:return 14;default:return 0;}
}
static int padbutton(Uint8 b){
  switch(b){case SDL_CONTROLLER_BUTTON_DPAD_LEFT:return 1;case SDL_CONTROLLER_BUTTON_DPAD_RIGHT:return 2;
  case SDL_CONTROLLER_BUTTON_DPAD_UP:return 3;case SDL_CONTROLLER_BUTTON_DPAD_DOWN:return 4;
  case SDL_CONTROLLER_BUTTON_A:return 5;case SDL_CONTROLLER_BUTTON_B:return 6;
  case SDL_CONTROLLER_BUTTON_X:return 7;case SDL_CONTROLLER_BUTTON_Y:return 8;
  case SDL_CONTROLLER_BUTTON_LEFTSHOULDER:return 9;case SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:return 10;
  case SDL_CONTROLLER_BUTTON_START:return 11;case SDL_CONTROLLER_BUTTON_BACK:return 12;case SDL_CONTROLLER_BUTTON_GUIDE:return 14;default:return 0;}
}
static void init_session(Synth *s){
  s->running=0;s->playing=0;s->amp_stage=0;s->amp_env=0;s->filter_env=0;
  s->lp1=s->lp2=s->lp3=s->lp4=0;
  defaults(&s->pat);s->pat.wave=0;s->pat.cutoff=52;s->pat.resonance=68;
  s->project_bpm=128;s->attack=0;s->sustain=60;s->release=18;s->filter_mode=0;
  s->pattern_count=1;s->edit_pattern=s->play_pattern=0;s->edit_bar=s->play_bar=0;
  bar_counts[0]=1;pattern_grid[0][0]=s->pat;s->play_pat=s->pat;
  s->chain_size=0;s->chain_on=0;s->play_chain_pos=0;s->playlist_cursor=0;s->menu=0;
  s->current=0;s->pos=-1;s->samples_to_step=0;s->chain_plus=s->chain_minus=0;s->dirty=1;
  undo_count=redo_count=0;
}
static void action(Synth *s,int key,int *sound_sel,int *save_requested,int *quit){
  SDL_LockAudioDevice(s->dev);
  if(key==13){*quit=1;}
  else if(key==11){s->running=!s->running;if(s->running){publish_bar(s);s->play_chain_pos=0;s->play_pattern=(s->chain_on&&s->chain_size)?s->chain_items[0]:s->edit_pattern;s->play_bar=0;s->play_pat=pattern_grid[s->play_pattern][0];s->pos=-1;s->samples_to_step=0.0;}else{s->playing=0;s->amp_stage=0;s->amp_env=0.0;s->filter_env=0.0;s->lp1=s->lp2=s->lp3=s->lp4=0.0;}}
  else if(key==12){s->menu=s->menu?0:1;}
  else if(s->menu==7){
    if(key==3)s->library_slot=(s->library_slot+LIB_SLOTS-1)%LIB_SLOTS;
    if(key==4)s->library_slot=(s->library_slot+1)%LIB_SLOTS;
    if(key==1)s->library_slot=CLAMP(s->library_slot-7,0,LIB_SLOTS-1);
    if(key==2)s->library_slot=CLAMP(s->library_slot+7,0,LIB_SLOTS-1);
    if(key==5 && library_exists(data_dir,s->library_type,s->library_slot))
      *save_requested=20+s->library_type;
    if(key==7)*save_requested=30+s->library_type; /* X: save selected slot */
    if(key==8 && library_exists(data_dir,s->library_type,s->library_slot))s->menu=8;
    if(key==6)s->menu=1;
  }
  else if(s->menu==8){
    if(key==5)*save_requested=40+s->library_type;
    if(key==5 || key==6)s->menu=7;
  }
  else if(s->menu==2){
    if(key==3)s->tool_cursor=(s->tool_cursor+6)%7;
    if(key==4)s->tool_cursor=(s->tool_cursor+1)%7;
    if(key==5){apply_tool(s,s->tool_cursor==6?7:s->tool_cursor);}
    if(key==6)s->menu=1;
  }
  else if(s->menu==5){
    if(key==3)s->project_field=(s->project_field+3)%4;
    if(key==4)s->project_field=(s->project_field+1)%4;
    int d=key==1?-1:key==2?1:key==15?-10:key==16?10:0;
    if(d && s->project_field==0){s->project_bpm=CLAMP(s->project_bpm+d,40,240);s->dirty=1;}
    if(d && s->project_field==1){select_pattern(s,CLAMP(s->edit_pattern+d,0,s->pattern_count-1));}
    if(key==5 && s->project_field==2)*save_requested=1;
    if(key==5 && s->project_field==3 && s->pattern_count<MAX_PATTERNS){
      publish_bar(s);int p=s->pattern_count++;bar_counts[p]=1;pattern_grid[p][0]=s->pat;select_pattern(s,p);
    }
    if(key==6)s->menu=1;
  }
  else if(s->menu==9){ /* pattern playlist editor: a block is a pattern ID */
    if(key==3)s->playlist_cursor=CLAMP(s->playlist_cursor-1,0,s->chain_size);
    if(key==4)s->playlist_cursor=CLAMP(s->playlist_cursor+1,0,s->chain_size);
    if((key==1||key==2) && s->playlist_cursor<s->chain_size){
      s->chain_items[s->playlist_cursor]=CLAMP(s->chain_items[s->playlist_cursor]+(key==1?-1:1),0,s->pattern_count-1);s->dirty=1;
    }
    if(key==5 && s->chain_size<CHAINS){
      int at=s->playlist_cursor;
      for(int j=s->chain_size;j>at;j--)s->chain_items[j]=s->chain_items[j-1];
      s->chain_items[at]=at>0?s->chain_items[at-1]:s->edit_pattern;
      s->chain_size++;s->playlist_cursor=CLAMP(at+1,0,s->chain_size);s->dirty=1;
    }
    if(key==8 && s->playlist_cursor<s->chain_size){
      for(int j=s->playlist_cursor;j<s->chain_size-1;j++)s->chain_items[j]=s->chain_items[j+1];
      s->chain_size--;s->playlist_cursor=CLAMP(s->playlist_cursor,0,s->chain_size);s->dirty=1;
      if(!s->chain_size)s->chain_on=0;
    }
    if(key==7){s->chain_on=!s->chain_on && s->chain_size>0;s->dirty=1;}
    if(key==6)s->menu=1;
  }
  else if(s->menu==10){if(key==5)init_session(s);else if(key==6)s->menu=1;}
  else if(s->menu==6){
    if(key==1 || key==2){checkpoint(s);s->pat.wave=CLAMP(s->pat.wave+(key==1?-1:1),0,5);}
    if(key==6)s->menu=1;
  }
  else if(s->menu==3 || s->menu==4){
    int *sel=s->menu==3?&s->preset_cursor:&s->seq_cursor;
    if(key==3)*sel=(*sel+7)%8;
    if(key==4)*sel=(*sel+1)%8;
    if(key==5){checkpoint(s);if(s->menu==3)sound_preset(s,*sel);else seq_preset(s,*sel);s->menu=0;}
    if(key==6)s->menu=1;
  }
  else if(s->menu){
    if(key==3)s->menu_cursor=(s->menu_cursor+10)%11;
    if(key==4)s->menu_cursor=(s->menu_cursor+1)%11;
    if(key==5){
      if(s->menu_cursor==0){s->menu=5;s->project_field=0;}
      else if(s->menu_cursor>=1 && s->menu_cursor<=3){s->library_type=s->menu_cursor-1;s->menu=7;}
      else if(s->menu_cursor==4){s->menu=3;s->preset_cursor=0;}
      else if(s->menu_cursor==5){s->menu=4;s->seq_cursor=0;}
      else if(s->menu_cursor==6)s->menu=6;
      else if(s->menu_cursor==7)s->menu=2;
      else if(s->menu_cursor==8)*save_requested=1;
      else if(s->menu_cursor==9){s->menu=9;s->playlist_cursor=0;}
      else if(s->menu_cursor==10)s->menu=10;
    }
    if(key==6)s->menu=0;
  }
  else if(s->page==0 && s->step_edit){
    Step *st=&s->pat.step[s->current];
    if(key==6){s->step_edit=0;}
    else if(key==9)s->step_field=(s->step_field+5)%6;
    else if(key==10)s->step_field=(s->step_field+1)%6;
    else if(key==5){checkpoint(s);st->on=!st->on;}
    
    else {
      int d=(key==1?-1:key==2?1:key==3?10:key==4?-10:0);
      if(d){
        checkpoint(s);
        switch(s->step_field){
          case 0:st->note=CLAMP(st->note+d,24,84);s->last_note=st->note;break;
          case 1:st->velocity=CLAMP(st->velocity+d,1,127);break;
          case 2:st->gate=CLAMP(st->gate+d,1,100);break;
          case 3:st->accent=d>0;break;
          case 4:st->slide=d>0;break;
          case 5:st->cutoff_lock=CLAMP(st->cutoff_lock+d,-1,100);break;
        }
      }
    }
  }
  else if(key==9){s->page=(s->page+2)%3;s->chain_plus=s->chain_minus=0;*sound_sel=0;}
  else if(key==10){s->page=(s->page+1)%3;s->chain_plus=s->chain_minus=0;*sound_sel=0;}
  else if(s->page==0){
    Step *st=&s->pat.step[s->current];
    if(key==1){
      if(s->chain_plus){s->chain_plus=0;s->current=15;}
      else if(s->chain_minus){s->chain_minus=0;if(s->edit_bar>0){select_bar(s,s->edit_bar-1);s->current=15;}}
      else if(s->current==0)s->chain_minus=1;
      else s->current--;
    }
    if(key==2){
      if(s->chain_minus){s->chain_minus=0;s->current=0;}
      else if(s->chain_plus){/* A confirms adding a bar */}
      else if(s->current==15){
        if(s->edit_bar+1<bar_counts[s->edit_pattern]){select_bar(s,s->edit_bar+1);s->current=0;}
        else if(bar_counts[s->edit_pattern]<MAX_BARS)s->chain_plus=1;
      }else s->current++;
    }
    if(key==3 || key==4){s->chain_plus=s->chain_minus=0;s->current=(s->current+8)%16;}
    if(key==5 && s->chain_plus){add_bar(s);}
    else if(key==5 && s->chain_minus){delete_bar(s);}
    else if(key==5){checkpoint(s);if(!st->on){st->note=s->last_note;st->on=1;}else s->last_note=st->note;s->step_edit=1;s->step_field=0;}
    if(key==6 && !s->chain_plus && !s->chain_minus){checkpoint(s);st->on=0;}
    if(key==7)apply_tool(s,2);
    if(key==8)apply_tool(s,3);
    } else if(s->page==1 || s->page==2){
    int pg=s->page==1,count=pg?4:9;
    if(key==3)*sound_sel=(*sound_sel+count-1)%count;
    if(key==4)*sound_sel=(*sound_sel+1)%count;
    int delta=key==1?-1:key==2?1:key==15?-10:key==16?10:0;
    if(delta){int *ad[]={&s->attack,&s->pat.decay,&s->sustain,&s->release};
      int *fx[]={&s->pat.cutoff,&s->pat.resonance,&s->pat.envmod,&s->filter_fm,&s->pat.drive,&s->slide_time,&s->mod_rate,&s->mod_depth,&s->filter_mode};
      int *v=pg?ad[*sound_sel]:fx[*sound_sel];int max=(!pg && *sound_sel==8)?1:100;
      if(max==5 || max==1)delta=delta<0?-1:1;
      checkpoint(s);*v=CLAMP(*v+delta,0,max);
    }
  }else{
    /* Legacy chain editor disabled: creation/navigation lives in SEQ via +. */
    if(key==6)s->page=0;
  }
  /* The editor and audio engine retain separate pattern pointers so browsing
     a chain never follows or interrupts playback.  When editing the pattern
     currently being heard, publish the changes immediately, under SDL audio
     lock. This removes the one-bar stale snapshot present in 0.7.1/0.7.2. */
  publish_bar(s);
  if(s->running && s->edit_pattern==s->play_pattern && s->edit_bar==s->play_bar){
    int old_note=-1;
    int old_on=0;
    if(s->pos>=0 && s->pos<STEPS){
      old_note=s->play_pat.step[s->pos].note;
      old_on=s->play_pat.step[s->pos].on;
    }
    s->play_pat=s->pat;
    if(s->pos>=0 && s->pos<STEPS && s->pos==s->current){
      Step *live=&s->play_pat.step[s->pos];
      if(live->on && s->playing && (live->note!=old_note || !old_on)){
        s->target=hz(live->note);
        /* Pitch edits should be audible in the current step; the next
           audio sample uses this frequency rather than waiting for tick. */
        s->freq=s->target;
      }
      if(!live->on && s->playing){
        s->playing=0;
        if(s->amp_stage!=0)s->amp_stage=4;
      }
    }
  }
  SDL_UnlockAudioDevice(s->dev);
}

int main(int argc,char **argv){
  const char *dir=argc>1?argv[1]:".";
  snprintf(data_dir,sizeof(data_dir),"%s",dir);
  defaults(&syn.pat);
  for(int i=0;i<BANKS;i++){syn.bank[i]=syn.pat;syn.chain[i]=i;}
  syn.chain_len=1;syn.chain[0]=0;
  syn.project_bpm=128;syn.sustain=60;syn.attack=0;syn.release=18;syn.slide_time=12;syn.mod_rate=20;syn.filter_mode=0;init_session(&syn);load(&syn,dir);syn.play_pat=syn.pat;syn.pos=-1;syn.current=0;syn.last_note=syn.pat.step[0].note;syn.noise_seed=0xA51Du;syn.target=syn.freq=hz(36);
  SDL_SetHint("SDL_VIDEO_ALLOW_SCREENSAVER","0");
  SDL_SetHint("SDL_AUDIO_DEVICE_APP_NAME","Antresoli SX");
  if(SDL_Init(SDL_INIT_VIDEO|SDL_INIT_AUDIO|SDL_INIT_GAMECONTROLLER)<0){fprintf(stderr,"SDL_Init: %s\n",SDL_GetError());return 1;}
  SDL_DisableScreenSaver();
  fprintf(stderr,"Antresoli SX: SDL screensaver disabled; OS-level suspend must be disabled separately in muOS settings.\n");
  SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY,"0");
  SDL_Window *w=SDL_CreateWindow("ANTRESOLI SX",SDL_WINDOWPOS_CENTERED,SDL_WINDOWPOS_CENTERED,640,480,SDL_WINDOW_SHOWN);
  if(!w){fprintf(stderr,"window: %s\n",SDL_GetError());SDL_Quit();return 1;}
  SDL_Renderer *r=SDL_CreateRenderer(w,-1,SDL_RENDERER_ACCELERATED|SDL_RENDERER_PRESENTVSYNC);
  if(!r)r=SDL_CreateRenderer(w,-1,SDL_RENDERER_SOFTWARE);
  if(!r){fprintf(stderr,"renderer: %s\n",SDL_GetError());SDL_DestroyWindow(w);SDL_Quit();return 1;}
  SDL_AudioSpec want={0};want.freq=SR;want.format=AUDIO_F32SYS;want.channels=2;want.samples=256;want.callback=audio_cb;want.userdata=&syn;
  syn.dev=SDL_OpenAudioDevice(NULL,0,&want,&syn.actual,0);
  if(!syn.dev){fprintf(stderr,"audio: %s\n",SDL_GetError());SDL_DestroyRenderer(r);SDL_DestroyWindow(w);SDL_Quit();return 1;}
  if(syn.actual.freq!=SR||syn.actual.format!=AUDIO_F32SYS||syn.actual.channels!=2){fprintf(stderr,"unsupported audio format\n");SDL_CloseAudioDevice(syn.dev);SDL_DestroyRenderer(r);SDL_DestroyWindow(w);SDL_Quit();return 1;}
  SDL_GameController *pad=NULL;for(int i=0;i<SDL_NumJoysticks();i++)if(SDL_IsGameController(i)){pad=SDL_GameControllerOpen(i);break;}
  SDL_PauseAudioDevice(syn.dev,0);
  int quit=0,sel=0,saved=0,save_requested=0;
  int held=0;Uint32 held_start=0,held_next=0;
  int menu_down=0,start_down=0,exit_combo=0;
  Uint32 combo_start=0;
  Uint32 last_audio_check=0, last_progress_check=0;
  uint64_t last_frame=0;
  while(!quit){
    Uint32 poll_ms=SDL_GetTicks();
    if(poll_ms-last_audio_check>=1000){
      last_audio_check=poll_ms;
      SDL_AudioStatus status=SDL_GetAudioDeviceStatus(syn.dev);
      if(status==SDL_AUDIO_PAUSED){fprintf(stderr,"[AUDIO] SDL device PAUSED at %u ms; resume\n",(unsigned)poll_ms);SDL_PauseAudioDevice(syn.dev,0);}
      else if(status==SDL_AUDIO_STOPPED){fprintf(stderr,"[AUDIO] SDL device STOPPED at %u ms (requires backend investigation)\n",(unsigned)poll_ms);}
    }
    if(poll_ms-last_progress_check>=3000){
      last_progress_check=poll_ms;
      SDL_LockAudioDevice(syn.dev);uint64_t n=syn.frame;int run=syn.running;SDL_UnlockAudioDevice(syn.dev);
      if(run && n==last_frame){
        fprintf(stderr,"[AUDIO WATCHDOG] callback not progressing at %u ms; rearming device\n",(unsigned)poll_ms);
        SDL_PauseAudioDevice(syn.dev,1);SDL_PauseAudioDevice(syn.dev,0);
      }
      last_frame=n;
    }
    SDL_Event e;
    while(SDL_PollEvent(&e)){
      if(e.type==SDL_QUIT){quit=1;continue;}
      if(e.type==SDL_APP_WILLENTERBACKGROUND || e.type==SDL_APP_DIDENTERBACKGROUND || e.type==SDL_APP_DIDENTERFOREGROUND || e.type==SDL_WINDOWEVENT){
        if(e.type!=SDL_WINDOWEVENT || e.window.event==SDL_WINDOWEVENT_FOCUS_LOST || e.window.event==SDL_WINDOWEVENT_FOCUS_GAINED)
          fprintf(stderr,"[SDL EVENT] type=%u window=%u tick=%u\n",(unsigned)e.type,e.type==SDL_WINDOWEVENT?(unsigned)e.window.event:0u,(unsigned)SDL_GetTicks());
      }
      if(e.type==SDL_CONTROLLERAXISMOTION && !syn.menu && !syn.step_edit){
        int k=e.caxis.axis==SDL_CONTROLLER_AXIS_TRIGGERLEFT?15:e.caxis.axis==SDL_CONTROLLER_AXIS_TRIGGERRIGHT?16:0;
        if(k){if(e.caxis.value>23000 && held!=k){action(&syn,k,&sel,&save_requested,&quit);held=k;held_start=SDL_GetTicks();held_next=held_start+300;}
          else if(e.caxis.value<10000 && held==k)held=0;}
        continue;
      }
      int down=(e.type==SDL_KEYDOWN || e.type==SDL_CONTROLLERBUTTONDOWN);
      int up=(e.type==SDL_KEYUP || e.type==SDL_CONTROLLERBUTTONUP);
      if(!down && !up)continue;
      if(e.type==SDL_KEYDOWN && e.key.repeat)continue;
      int k=(e.type==SDL_KEYDOWN || e.type==SDL_KEYUP)
          ?normkey(e.key.keysym.sym):padbutton(e.cbutton.button);
      if(!k)continue;
      if(k==14){menu_down=down?1:0; if(!menu_down)combo_start=0;continue;}
      if(k==11){
        if(down){start_down=1;}
        else {
          start_down=0;
          if(!exit_combo && !menu_down)action(&syn,11,&sel,&save_requested,&quit);
          if(!menu_down)exit_combo=0;
          combo_start=0;
        }
        continue;
      }
      if(down && menu_down && (k==9 || k==10)){
        SDL_LockAudioDevice(syn.dev);apply_tool(&syn,k==9?0:1);SDL_UnlockAudioDevice(syn.dev);
        continue;
      }
      if(down && !menu_down){
        action(&syn,k,&sel,&save_requested,&quit);
        if((k>=1&&k<=4)||k==15||k==16){
          held=k;held_start=SDL_GetTicks();held_next=held_start+300;
        }
      }
      if(up && k==held)held=0;
    }
    if(menu_down && start_down){
      if(!combo_start){combo_start=SDL_GetTicks();exit_combo=1;}
      else if(SDL_GetTicks()-combo_start>=700){exit_combo=1;quit=1;}
    }else combo_start=0;
    if(held){Uint32 now=SDL_GetTicks();if((Sint32)(now-held_next)>=0){repeat_edit=1;action(&syn,held,&sel,&save_requested,&quit);repeat_edit=0;held_next=now+(now-held_start>1000?40:100);}}
    if(save_requested){
      Synth snapshot;
      SDL_LockAudioDevice(syn.dev);snapshot=syn;SDL_UnlockAudioDevice(syn.dev);
      int command=save_requested;
      if(command==1){saved=(save(&snapshot,dir))?120:0;if(saved)syn.dirty=0;}
      else if(command==3)saved=save_sound(&snapshot,dir)?120:0;
      else if(command==5)saved=save_sequence(&snapshot,dir)?120:0;
      else if(command==4||command==6){
        SDL_LockAudioDevice(syn.dev);
        int ok=command==4?load_sound(&syn,dir):load_sequence(&syn,dir);
        SDL_UnlockAudioDevice(syn.dev);saved=ok?120:0;
      }
      else if(command>=20 && command<=22){
        SDL_LockAudioDevice(syn.dev);
        Synth before=syn;
        int ok=library_load(&syn,dir,command-20,syn.library_slot);
        if(!ok)syn=before;
        SDL_UnlockAudioDevice(syn.dev);
        saved=ok?120:0;if(ok)library_message="LOADED";
      }
      else if(command>=30 && command<=32){
        saved=library_save(&snapshot,dir,command-30,snapshot.library_slot)?120:0;if(saved)library_message="SAVED";
      }
      else if(command>=40 && command<=42){
        saved=library_delete(dir,command-40,snapshot.library_slot)?120:0;if(saved)library_message="DELETED";
      }
      save_requested=0;
    }
    Synth frame_snapshot; SDL_LockAudioDevice(syn.dev);frame_snapshot=syn;SDL_UnlockAudioDevice(syn.dev);render(r,&frame_snapshot,sel,saved);
    if(saved>0)--saved;
    SDL_Delay(16);
  }
  SDL_LockAudioDevice(syn.dev);Synth final_snapshot=syn;SDL_UnlockAudioDevice(syn.dev);save(&final_snapshot,dir);
  SDL_CloseAudioDevice(syn.dev);if(pad)SDL_GameControllerClose(pad);
  SDL_DestroyRenderer(r);SDL_DestroyWindow(w);SDL_EnableScreenSaver();SDL_Quit();return 0;
}
