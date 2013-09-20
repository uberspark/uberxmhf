To *run* [TrustVisor](../) on a given machine, installation is the
same as for any other [XMHF](../../xmhf) app. See [Installing
XMHF](../../xmhf/doc/installing-xmhf.md).

On a machine where you are planning to develop PALs, you will also
need to install the TrustVisor development headers. The
[tee-sdk](../../tee-sdk) currently expects those headers to be
installed in two places.

First install the headers in a 'normal' system location. Assuming
you've already run `./configure` from the `XMHF` directory:

    make install-dev

You will then need to reconfigure to point to the PAL
cross-compilation environment, and install the headers again:

    ./configure --with-approot=/path/to/tv --prefix=/usr/local/i586-tsvc
    make install-dev
