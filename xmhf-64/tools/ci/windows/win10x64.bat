echo Hello world

:: Identify OS type

F:\test32.exe 1001000064
F:\test32.exe 1001000064
F:\test32.exe 1001000064

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

:: Test amd64 pal_demo

F:\test64.exe 1100000064
F:\test64.exe 1100000064
F:\test64.exe 1100000064

F:\test_args64.exe 7 7 7

IF %ERRORLEVEL% EQU 0 GOTO success64
F:\test64.exe 1200000064
F:\test64.exe 1200000064
F:\test64.exe 1200000064
F:\test64.exe 1444444444
pause
exit 1

:success64
F:\test64.exe 1300000064
F:\test64.exe 1300000064
F:\test64.exe 1300000064

:: End test

F:\test32.exe 1555555555
F:\test32.exe 1555555555
F:\test32.exe 1555555555

echo Bye world
pause
exit 0

