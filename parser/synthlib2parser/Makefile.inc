BUILD_SUFFIX=debug
OPTFLAGS=-ggdb3 -O0 -fno-inline
FEAT_FLAGS=-fPIC

ifeq ($(MAKECMDGOALS), opt)
BUILD_SUFFIX=opt
OPTFLAGS=-O2
endif
ifeq ($(MAKECMDGOALS), optlto)
BUILD_SUFFIX=opt
OPTFLAGS=-O2 -flto
endif
ifeq ($(MAKECMDGOALS), prof)
BUILD_SUFFIX=prof
OPTFLAGS=-O2 -pg
endif
ifeq ($(MAKECMDGOALS), proflto)
BUILD_SUFFIX=prof
OPTFLAGS=-O2 -pg -flto
endif
ifeq ($(MAKECMDGOALS), eopt)
BUILD_SUFFIX=opt
OPTFLAGS=-O3
endif
ifeq ($(MAKECMDGOALS), eoptlto)
BUILD_SUFFIX=opt
OPTFLAGS=-O3 -flto
endif
ifeq ($(MAKECMDGOALS), eprof)
BUILD_SUFFIX=prof
OPTFLAGS=-O3 -pg
endif
ifeq ($(MAKECMDGOALS), eproflto)
BUILD_SUFFIX=prof
OPTFLAGS=-O3 -pg -flto
endif
ifeq ($(MAKECMDGOALS), gperf)
BUILD_SUFFIX=prof
OPTFLAGS=-O3
LINKFLAGS+=-lprofiler
endif

CXX=g++
CC=$(CXX)
LD=$(CXX)
CXXFLAGS+=-Wall -pedantic -Wno-write-strings -Wno-unused-function -D__STDC_LIMIT_MACROS
CXXFLAGS+=-pipe -std=c++11 -I $(SYNTH_LIB_PARSER_ROOT)/src/include
CXXFLAGS+=$(FEAT_FLAGS)
AR=ar
ARFLAGS=rcs
BISON=bison -v
FLEX=flex

CXXPRINTNAME="[CXX:$(PROJECT_NAME)]"
ARPRINTNAME="[AR:$(PROJECT_NAME)]"
LDPRINTNAME="[LD:$(PROJECT_NAME)]"
DEPPRINTNAME="[DEP:$(PROJECT_NAME)]"
BISONPRINTNAME="[bison:$(PROJECT_NAME)]"
FLEXPRINTNAME="[flex:$(PROJECT_NAME)]"
.PHONY:				debug clean opt prof all default eprof eopt optlto proflto eoptlto eproflto
