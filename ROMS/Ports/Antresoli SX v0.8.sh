#!/bin/sh
# Antresoli SX v0.8 Pattern Architecture for RG35XX-2024 / muOS Jacaranda
# Never force SDL video drivers: muOS selects working backend.
DIR=""
for BASE in /mnt/mmc /mnt/sdcard /mnt/SDCARD /mnt/SDCARD2; do
    if [ -d "$BASE/ports/antresoli-sx-v08" ]; then
        DIR="$BASE/ports/antresoli-sx-v08"
        break
    fi
done
[ -n "$DIR" ] || exit 1
cd "$DIR" || exit 1
exec > "$DIR/log.txt" 2>&1
echo '=== Antresoli SX v0.8 Pattern Architecture ==='
date
uname -a
# Clean v0.8 storage: never import older project files.
unset SDL_VIDEODRIVER
unset SDL_FBDEV
export SDL_AUDIODRIVER=alsa
if [ ! -f ./antresoli-sx ]; then echo 'Binary not found. Build in WSL first.'; exit 127; fi
./antresoli-sx "$DIR"
CODE=$?
echo "Exit code: $CODE"
sync
exit "$CODE"
