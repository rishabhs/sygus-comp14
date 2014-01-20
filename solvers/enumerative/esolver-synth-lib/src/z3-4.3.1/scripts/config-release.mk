CC=gcc
PREFIX=/usr
CXX=g++
CXXFLAGS= -D_MP_INTERNAL -D_AMD64_ -D_USE_THREAD_LOCAL  -fopenmp -mfpmath=sse -fno-strict-aliasing -fPIC -c -O3 -D _EXTERNAL_RELEASE -fomit-frame-pointer -msse -msse2 
LTOFLAG=-flto=jobserver
CXX_OUT_FLAG=-o 
OBJ_EXT=.o
LTO_OBJ_EXT=-lto.o
LIB_EXT=.a
LTO_LIB_EXT=-lto.a
AR=ar
AR_FLAGS=rcs
AR_OUTFLAG= 
EXE_EXT=
LINK=g++
LINK_FLAGS=-flto=jobserver -O3
LINK_OUT_FLAG=-o 
LINK_EXTRA_FLAGS=-lpthread  -fopenmp -lrt
SO_EXT=.so
SLINK=g++
SLINK_FLAGS= -shared -flto -O3
SLINK_EXTRA_FLAGS= -fopenmp -lrt
SLINK_OUT_FLAG=-o 
