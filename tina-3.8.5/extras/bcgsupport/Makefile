# makefile for libbcg

# CADP installation directory, please update:
# CADP=/usr/local/cadp
# CADP=/opt/cadp
CADP=/home/bernard/cadp

# architecture
# note: bcg support cannot be installed for x64, mac64, sol64 since CADP libs are not compiled with -fPIC.
# hence set ARCH to one of
#  iX86 (linux 32b)
#  win32
#  win64
ARCH=iX86
BCGLIBS=$(CADP)/bin.$(ARCH)
BCGINCL=$(CADP)/incl

ifeq ($(ARCH),win32)
# windows 32b (mingw)
DLLEXT=.dll
TGT=-m32
else
ifeq ($(ARCH),win64)
# windows 64b (mingw)
DLLEXT=.dll
TGT=-m64
else
# linux 32b
DLLEXT=.so
TGT=-m32
endif
endif


build:
	$(MAKE) bcglib

bcglib: bcg_lib.c
	rm -f libbcg$(DLLEXT)
	gcc $(TGT) -O2 -o libbcg$(DLLEXT) bcg_lib.c -shared -s -Wall -I$(BCGINCL) $(BCGLIBS)/libBCG.a  $(BCGLIBS)/libBCG_IO.a  -lm


