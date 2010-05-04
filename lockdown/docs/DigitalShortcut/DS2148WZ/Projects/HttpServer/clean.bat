REM - Clean the Project, Remove: *.o, *.lst and HttpServ.* files
del *.o
del *.lst
del HttpServ.*
cd Wiznet
del *.o
del *.lst
cd..
cd utils
del *.o
del *.lst
cd..
cd ARM2148
del *.o
del *.lst
cd..
cd DigiShort
del *.o
del *.lst
cd..
cd http
del *.o
del *.lst
cd..
cd i2c
del *.o
del *.lst
cd..
REM - Clean "Dependencies"
cd .dep
del *.* /Q
cd..