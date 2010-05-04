REM Combine JWH-Demo-http Code-JWDemoHttp.hex with WebSite Image-siteArm.bin (result JWHttp_ful.hex file)
REM S: logical drive initialized by sub_S.bat in 
REM		C:\Documents and Settings\Usr_XX\Start Menu\Programs\Startup
S:\DS2148WZ\Tools\srec_cat JWDemoHttp.hex -intel S:\DS2148WZ\SiteBuilder\dsweb\SiteBuilderGenerated\siteArm.bin -binary -offset 0x30000 -o JWHttp_ful.hex -intel -address-length=2 
