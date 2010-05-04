**** LedBlink ReadMe ****

LedBlink is a very simple C Project consisting of several routines only.

In perpetual loop it:
 - toggles P0.4 pin - on connector P3(13)
 - blinks Led connected to LPC2148 P1.24 pin
 - sends '*' character to console every second.
Blinking is in Morse style: dash, dash, dot, dot, dot, pause.

Serial Console operates on 115200 kBauds, 8bits, Noparity.
After Power-up or Reset Short Sign-On message: "### Blink Led (Morse)... ###" should appear on console screen.
Small Command Interpretter with 2 commands: L and I is present to allow user interactions.
L (loop) command - loops ToggleP0.5 routine, check P3(15) with the scope.
I (info) "printfs" info message on console.
Timer0 is initialized to generate interrupts every 1msec.

The MK.Bat compiles (arm-elf GNU tool chain) all files and creates Led_Blink.hex together with *.elf *.dmp *.map files.
After unziping WZ2148WZ package modify subst Path in MK.Bat to reflect your Actual Project Path.
The Hex file is used by Philips Flash Utility to load the code to LPC2148 Flash memory.

Philips Flash Utility (LPC2000 Flash Utility V2.2.3) Settings:
Connected to Port: COM1
Use Baud Rate: 38400
Use DTR/RTS for Reset...: Checked
Device: LPC2148
XTAL Freq[kHz]: 12000
After pressing ReadDevice ID button PartID should be 67305253

It is "novice startup project" example ready for changes and migrations.


