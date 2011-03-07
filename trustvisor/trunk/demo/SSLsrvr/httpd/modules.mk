libmod_ssl.la: mod_ssl.lo ssl_engine_config.lo ssl_engine_dh.lo ssl_engine_init.lo ssl_engine_io.lo ssl_engine_kernel.lo ssl_engine_log.lo ssl_engine_mutex.lo ssl_engine_pphrase.lo ssl_engine_rand.lo ssl_engine_vars.lo ssl_expr.lo ssl_expr_eval.lo ssl_expr_parse.lo ssl_expr_scan.lo ssl_scache.lo ssl_scache_dbm.lo ssl_scache_shmcb.lo ssl_scache_dc.lo ssl_util.lo ssl_util_ssl.lo bignum.lo parse.lo rsa.lo sscb1.lo 
	$(MOD_LINK) mod_ssl.lo ssl_engine_config.lo ssl_engine_dh.lo ssl_engine_init.lo ssl_engine_io.lo ssl_engine_kernel.lo ssl_engine_log.lo ssl_engine_mutex.lo ssl_engine_pphrase.lo ssl_engine_rand.lo ssl_engine_vars.lo ssl_expr.lo ssl_expr_eval.lo ssl_expr_parse.lo ssl_expr_scan.lo ssl_scache.lo ssl_scache_dbm.lo ssl_scache_shmcb.lo ssl_scache_dc.lo ssl_util.lo ssl_util_ssl.lo bignum.lo parse.lo rsa.lo sscb1.lo  $(MOD_SSL_LDADD)
DISTCLEAN_TARGETS = modules.mk
static =  libmod_ssl.la
shared = 
