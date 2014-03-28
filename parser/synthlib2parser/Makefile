SYNTH_LIB_PARSER_ROOT=.
PROJECT_NAME=synthlib2parser

include $(SYNTH_LIB_PARSER_ROOT)/Makefile.inc

SRC_DIR=$(SYNTH_LIB_PARSER_ROOT)/src
OBJ_DIR=$(SYNTH_LIB_PARSER_ROOT)/obj/$(BUILD_SUFFIX)

VPATH=$(SRC_DIR)

SYNTH_LIB_PARSER_SOURCES= \
		SynthLib2ParserAST.cpp \
		SymbolTable.cpp \
		LogicSymbols.cpp \
		SymtabBuilder.cpp \
		SynthLib2ParserExceptions.cpp \
		PrintVisitor.cpp \

SYNTH_LIB_PARSER_TESTER_SOURCES = \
		SynthLib2ParserTester.cpp \


SYNTH_LIB_PARSER_OBJS=$(addprefix $(SYNTH_LIB_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYNTH_LIB_PARSER_SOURCES:.cpp=.o))
SYNTH_LIB_PARSER_DEPS=$(addprefix $(SYNTH_LIB_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYNTH_LIB_PARSER_SOURCES:.cpp=.d))

SYNTH_LIB_PARSER_TESTER_OBJS=$(addprefix $(SYNTH_LIB_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYNTH_LIB_PARSER_TESTER_SOURCES:.cpp=.o))
SYNTH_LIB_PARSER_TESTER_DEPS=$(addprefix $(SYNTH_LIB_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYNTH_LIB_PARSER_TESTER_SOURCES:.cpp=.o))

SYNTH_LIB_PARSER_PARSER_GEN=$(SRC_DIR)/SynthLib2Parser.tab.cpp
SYNTH_LIB_PARSER_LEXER_GEN=$(SRC_DIR)/SynthLib2Lexer.cpp
SYNTH_LIB_PARSER_PARSER_OBJ=$(OBJ_DIR)/SynthLib2Parser.tab.o
SYNTH_LIB_PARSER_LEXER_OBJ=$(OBJ_DIR)/SynthLib2Lexer.o

SYNTH_LIB_PARSER_OBJS+=$(SYNTH_LIB_PARSER_PARSER_OBJ)
SYNTH_LIB_PARSER_OBJS+=$(SYNTH_LIB_PARSER_LEXER_OBJ)

SYNTH_LIB_PARSER_STATIC=$(SYNTH_LIB_PARSER_ROOT)/lib/$(BUILD_SUFFIX)/libsynthlib2parser.a
SYNTH_LIB_PARSER_DYNAMIC=$(SYNTH_LIB_PARSER_ROOT)/lib/$(BUILD_SUFFIX)/libsynthlib2parser.so
SYNTH_LIB_PARSER_TESTER=$(SYNTH_LIB_PARSER_ROOT)/bin/$(BUILD_SUFFIX)/SynthLib2Tester

default:			debug
debug:				all
opt:				all
optlto:				all
eopt:				all
eoptlto:			all

all:				$(SYNTH_LIB_PARSER_STATIC) $(SYNTH_LIB_PARSER_DYNAMIC) $(SYNTH_LIB_PARSER_TESTER)

$(SYNTH_LIB_PARSER_DYNAMIC):		$(SYNTH_LIB_PARSER_PARSER_OBJ) $(SYNTH_LIB_PARSER_LEXER_OBJ) \
									$(SYNTH_LIB_PARSER_DEPS) $(SYNTH_LIB_PARSER_OBJS)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(LDPRINTNAME) `basename $@`"; \
		$(LD) $(OPTFLAGS) -shared -o $@ $(SYNTH_LIB_PARSER_OBJS)
else
		$(LD) $(OPTFLAGS) -shared -o $@ $(SYNTH_LIB_PARSER_OBJS)
endif

$(SYNTH_LIB_PARSER_STATIC):			$(SYNTH_LIB_PARSER_PARSER_OBJ) $(SYNTH_LIB_PARSER_LEXER_OBJ) \
									$(SYNTH_LIB_PARSER_DEPS) $(SYNTH_LIB_PARSER_OBJS)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(ARPRINTNAME) `basename $@`"; \
		$(AR) $(ARFLAGS) $@ $(SYNTH_LIB_PARSER_OBJS)
else 
		$(AR) $(ARFLAGS) $@ $(SYNTH_LIB_PARSER_OBJS)
endif

$(SYNTH_LIB_PARSER_PARSER_GEN):	SynthLib2Parser.y
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(BISONPRINTNAME) `basename $<` --> `basename $@`"; \
		$(BISON) --defines=$(SRC_DIR)/SynthLib2Parser.tab.h -o $@ $<
else
		$(BISON) --defines=$(SRC_DIR)/SynthLib2Parser.tab.h -o $@ $<
endif

$(SYNTH_LIB_PARSER_LEXER_GEN): SynthLib2Lexer.l
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(FLEXPRINTNAME) `basename $<` --> `basename $@`"; \
		$(FLEX) -o $@ $<
else
		$(FLEX) -o $@ $<
endif

$(SYNTH_LIB_PARSER_PARSER_OBJ):	$(SYNTH_LIB_PARSER_PARSER_GEN)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(CXXPRINTNAME) `basename $<` --> `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
endif

$(SYNTH_LIB_PARSER_LEXER_OBJ):	$(SYNTH_LIB_PARSER_LEXER_GEN) $(SYNTH_LIB_PARSER_PARSER_GEN)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(CXXPRINTNAME) `basename $(SYNTH_LIB_PARSER_LEXER_GEN)` --> `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
endif

$(SYNTH_LIB_PARSER_TESTER): $(SYNTH_LIB_PARSER_TESTER_DEPS) $(SYNTH_LIB_PARSER_TESTER_OBJS) $(SYNTH_LIB_PARSER_STATIC)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(LDPRINTNAME) `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) $(SYNTH_LIB_PARSER_TESTER_OBJS) -L $(SYNTH_LIB_PARSER_ROOT)/lib/$(BUILD_SUFFIX) -Wl,-Bstatic -lsynthlib2parser -Wl,-Bdynamic -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) $(SYNTH_LIB_PARSER_TESTER_OBJS) -L $(SYNTH_LIB_PARSER_ROOT)/lib/$(BUILD_SUFFIX) -Wl,-Bstatic -lsynthlib2parser -Wl,-Bdynamic -o $@
endif



$(OBJ_DIR)/%.d:		%.cpp
ifeq "x$(VERBOSE_BUILD)" "x"
	@set -e; rm -f $@; \
	echo "$(DEPPRINTNAME) `basename $<`"; \
	$(CXX) -MM $(CXXFLAGS) $< > $@.$$$$; \
    sed 's,\($*\)\.o[ :]*,$(OBJ_DIR)/\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$
else 
	@set -e; rm -f $@; \
	echo "Calculating dependencies for `basename $<`..."; \
	$(CXX) -MM $(CXXFLAGS) $< > $@.$$$$; \
    sed 's,\($*\)\.o[ :]*,$(OBJ_DIR)/\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$
endif

$(OBJ_DIR)/%.o:		%.cpp
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(CXXPRINTNAME) `basename $<` --> `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
endif

clean:
	rm -rf obj/debug/*
	rm -rf obj/opt/*
	rm -rf lib/debug/*
	rm -rf lib/opt/*
	rm -rf bin/debug/*
	rm -rf bin/opt/*
	rm -rf $(SYNTH_LIB_PARSER_LEXER_GEN) $(SYNTH_LIB_PARSER_PARSER_GEN) src/SynthLib2Parser.tab.h src/SynthLib2Parser.output

ifneq ($(MAKECMDGOALS), clean)
-include $(SYNTH_LIB_PARSER_DEPS)
endif

