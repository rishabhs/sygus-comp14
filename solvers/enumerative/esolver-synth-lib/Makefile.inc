BUILD_SUFFIX=debug
OPTFLAGS=-ggdb3 -O0 -fno-inline
FEAT_FLAGS=-fPIC

Z3DIR=$(ESOLVER_ROOT)/src/z3-4.3.1
Z3LIBLINK=-lz3
Z3BUILDDIR=$(Z3DIR)/build

ifeq ($(MAKECMDGOALS), opt)
BUILD_SUFFIX=opt
OPTFLAGS=-O2
endif
ifeq ($(MAKECMDGOALS), optlto)
BUILD_SUFFIX=opt
OPTFLAGS=-O2 -flto
Z3LIBNAME=-lz3
endif
ifeq ($(MAKECMDGOALS), prof)
BUILD_SUFFIX=prof
OPTFLAGS=-O2 -pg
endif
ifeq ($(MAKECMDGOALS), proflto)
BUILD_SUFFIX=prof
OPTFLAGS=-O2 -pg -flto
Z3LIBLINK=-lz3
endif
ifeq ($(MAKECMDGOALS), eopt)
BUILD_SUFFIX=opt
OPTFLAGS=-O3
endif
ifeq ($(MAKECMDGOALS), eoptlto)
BUILD_SUFFIX=opt
OPTFLAGS=-O3 -flto
Z3LIBLINK=-lz3
endif
ifeq ($(MAKECMDGOALS), eprof)
BUILD_SUFFIX=prof
OPTFLAGS=-O3 -pg
endif
ifeq ($(MAKECMDGOALS), eproflto)
BUILD_SUFFIX=prof
OPTFLAGS=-O3 -pg -flto
Z3LIBLINK=-lz3
endif
ifeq ($(MAKECMDGOALS), fulllto)
BUILD_SUFFIX=opt
Z3LIBLINK=-lz3-lto
endif
ifeq ($(MAKECMDGOALS), fullltoprof)
BUILD_SUFFIX=prof
Z3LIBLINK=-lz3-lto
endif

CXX=g++
CC=$(CXX)
LD=$(CXX)
CXXFLAGS+=-Wall -pedantic -D__STDC_LIMIT_MACROS -DDISABLE_STATIC_BP
CXXFLAGS+=-I $(Z3DIR)/src/api/
CXXFLAGS+=-pipe -std=c++11
LINKFLAGS+=-L $(Z3BUILDDIR) -L $(ESOLVER_ROOT)/lib/$(BUILD_SUFFIX)
LINKFLAGS+=-Wl,-Bstatic -lesolver -Wl,-Bstatic $(Z3LIBLINK) -Wl,-Bdynamic -lrt
LINKFLAGS+=-lboost_program_options -lboost_system -fopenmp
CXXFLAGS+=$(FEAT_FLAGS)
AR=ar
ARFLAGS=rcs

CXXPRINTNAME="[CXX:$(PROJECT_NAME)]"
ARPRINTNAME="[AR:$(PROJECT_NAME)]"
LDPRINTNAME="[LD:$(PROJECT_NAME)]"
DEPPRINTNAME="[DEP:$(PROJECT_NAME)]"
.PHONY:				debug clean opt prof all default eprof eopt optlto proflto eoptlto eproflto
