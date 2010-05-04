<?php 
header( "Cache-Control: no-cache, must-revalidate" );
echo substr( (lcg_value() * 3.3), 0, 5); 
# SiteBuilder statements start with "#--sbHdr"
#--sbHdrAdd "HTTP/1.1 200 OK"
#--sbHdrAdd "Server: DSX50-WZ demo"
#--sbHdrAdd "Content-Type: text/html"                
#--sbHdrAdd "Cache-Control: no-cache, must-revalidate" 
#--sbHdrAdd "Content-Length: 8"           
#--sbHdrTail 01 FF;   # proc id = 01, 
?>
