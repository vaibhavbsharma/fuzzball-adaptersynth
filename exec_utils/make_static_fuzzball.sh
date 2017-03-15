#!/bin/bash
# 1. Run the ocamlfind ocamlopt command with the -verbose to get the ocamlopt command
# 2. Run the ocamlopt command with -dstartup to get fuzzball.startup.s and the gcc command
# 3. Modify the gcc command with
#  (1) replacing every instance of -lz with  '/usr/lib/x86_64-linux-gnu/libz.a'
#  (2) replacing every instance of -lstdc++ with '/usr/lib/gcc/x86_64-linux-gnu/4.8/libstdc++.a
#  (3) adding the -static-libgcc to statically link with the GNU C library 
#  (4) add the /usr/lib/gcc/x86_64-linux-gnu/4.8/libgcc.a at the of the gcc command
# 4. Run the modified gcc command to get fuzzball with statically compiled 
#    libz, libstdc++, and libgcc. fuzzball will now depend on
#    libm.so, libdl.so, libc.so, and ld.so being loaded dynamically.
#
# ocamlfind ocamlopt \
# -verbose \
# -dstartup \
# -package str,extlib,unix -linkpkg \
# -I ../ocaml -I ../trace -I ../execution -I ../stp/ocaml \
# -g stpvc.cmxa vine.cmxa trace.cmxa execution.cmxa \
# -o fuzzball \
# fuzzball.cmx

# gcc -static-libgcc -o 'fuzzball'   '-L../ocaml' '-L../trace' '-L../execution' '-L../stp/ocaml' '-L/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/site-lib/extlib' '-L/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml' -L/export/scratch/vaibhav/vex-r3206/trunk/ -L/export/scratch/vaibhav/fuzzball-adaptorsynth/src -L/export/scratch/vaibhav/binutils-2.23.2/lib -L/export/scratch/vaibhav/binutils-2.23.2/bfd -L/export/scratch/vaibhav/binutils-2.23.2/libiberty -L../libasmir/src -L../stp -L../stp/ocaml -L/export/scratch/vaibhav/vex-r3206/trunk/ -L/export/scratch/vaibhav/fuzzball-adaptorsynth/src -L/export/scratch/vaibhav/binutils-2.23.2/lib -L/export/scratch/vaibhav/binutils-2.23.2/bfd -L/export/scratch/vaibhav/binutils-2.23.2/libiberty -L../libasmir/src -L../stp -L../stp/ocaml -L/export/scratch/vaibhav/vex-r3206/trunk/ -L/export/scratch/vaibhav/fuzzball-adaptorsynth/src -L/export/scratch/vaibhav/binutils-2.23.2/lib -L/export/scratch/vaibhav/binutils-2.23.2/bfd -L/export/scratch/vaibhav/binutils-2.23.2/libiberty -L../libasmir/src -L../stp -L../stp/ocaml -L.. 'fuzzball.startup.s' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/std_exit.o' 'fuzzball.o' '../execution/execution.a' '../trace/trace.a' '../ocaml/vine.a' '../stp/ocaml/stpvc.a' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/unix.a' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/site-lib/extlib/extLib.a' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/str.a' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/stdlib.a' '-lasmir' '-lvex' '-lopcodes' '-lbfd' '-liberty' '/usr/lib/gcc/x86_64-linux-gnu/4.8/libstdc++.a' '-lasmir' '-lvex' '-lopcodes' '-lbfd' '-liberty' '/usr/lib/gcc/x86_64-linux-gnu/4.8/libstdc++.a' '-lvine_stubs' '-lasmir' '-lvex' '-lopcodes' '-lbfd' '-liberty'  '/usr/lib/x86_64-linux-gnu/libz.a' '/usr/lib/gcc/x86_64-linux-gnu/4.8/libstdc++.a' '-lcamlidl' '-lstpvc_stubs' '-lstp' '/usr/lib/gcc/x86_64-linux-gnu/4.8/libstdc++.a' '-lcamlidl' '-lunix' '-lcamlstr' '/home/fac05/mccamant/soft/amd64/caml/ocaml/4.02.1/lib/ocaml/libasmrun.a' -lm  -ldl   '/usr/lib/gcc/x86_64-linux-gnu/4.8/libgcc.a'
