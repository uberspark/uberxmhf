REM - Concatenate HttpServ(Addr 0) with siteArm(Addr 0x30000)
srec_cat HttpServ.hex -intel siteArm.bin -binary -offset 0x30000 -o httpsrv_ful.hex -intel -address-length=2 

