The TrustVisor build is primarily driven from the [XMHF](../../../xmhf)
build process; see [Building XMHF](../../../xmhf/doc/building-xmhf.md). When
running `configure`, you will need to set `--with-approot=hypapps/trustvisor` 
to point to the TrustVisor source code. To install trustvisor
development headers, please use `./configure --prefix=...` to specify
the install path, and run `make install-dev`.
