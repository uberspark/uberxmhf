echo Hello world

:: Identify OS type

F:\test32.exe 1001000086
F:\test32.exe 1001000086
F:\test32.exe 1001000086

:: Test i386 pal_demo

F:\test32.exe 1100000032
F:\test32.exe 1100000032
F:\test32.exe 1100000032

F:\test_args32.exe 7 7 7

IF %ERRORLEVEL% EQU 0 GOTO success32
F:\test32.exe 1200000032
F:\test32.exe 1200000032
F:\test32.exe 1200000032
F:\test32.exe 1444444444
pause
exit 1

:success32
F:\test32.exe 1300000032
F:\test32.exe 1300000032
F:\test32.exe 1300000032

:: End test

F:\test32.exe 1555555555
F:\test32.exe 1555555555
F:\test32.exe 1555555555

echo Bye world
pause
exit 0

