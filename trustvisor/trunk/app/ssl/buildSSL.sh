make
make install
objdump -D /usr/local/nssl/lib/libssl.so.0.9.8 > nlib.D
echo THUNK_ADDR 0x`grep "<__i686.get_pc_thunk.bx>:" nlib.D | cut -c 1-8` 
echo ENTRY_ADDR 0x`grep "<sscb2>:" nlib.D | cut -c 1-8` 
echo TEXT_ADDR 0x`grep "<scode_unseal>:" nlib.D | cut -c 1-8` 
echo DATA_ADDR 0x`grep "<sdatajunk2>:" nlib.D | cut -c 1-8`
echo PARAM_ADDR 0x`grep "<paramjunk2>:" nlib.D | cut -c 1-8`
echo STACK_ADDR 0x`grep "<stackjunk2>:" nlib.D | cut -c 1-8`
