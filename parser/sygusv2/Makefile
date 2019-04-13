SYGUS2_PARSER_ROOT=.
PROJECT_NAME=sygus2parser

include $(SYGUS2_PARSER_ROOT)/Makefile.inc

SRC_DIR=$(SYGUS2_PARSER_ROOT)/src
OBJ_DIR=$(SYGUS2_PARSER_ROOT)/obj/$(BUILD_SUFFIX)

VPATH=$(SRC_DIR)

SYGUS2_PARSER_SOURCES= \
	Sygus2ParserExceptions.cpp \
	Sygus2ParserAST.cpp \
	SymbolTable.cpp \
	TheoryManager.cpp

SYGUS2_PARSER_OBJS=$(addprefix $(SYGUS2_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYGUS2_PARSER_SOURCES:.cpp=.o))
SYGUS2_PARSER_DEPS=$(addprefix $(SYGUS2_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYGUS2_PARSER_SOURCES:.cpp=.d))

SYGUS2_PARSER_TESTER_OBJS=$(addprefix $(SYGUS2_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYGUS2_PARSER_TESTER_SOURCES:.cpp=.o))
SYGUS2_PARSER_TESTER_DEPS=$(addprefix $(SYGUS2_PARSER_ROOT)/obj/$(BUILD_SUFFIX)/, $(SYGUS2_PARSER_TESTER_SOURCES:.cpp=.o))

SYGUS2_PARSER_PARSER_GEN=$(SRC_DIR)/Sygus2Parser.tab.cpp
SYGUS2_PARSER_LEXER_GEN=$(SRC_DIR)/Sygus2Lexer.tab.cpp
SYGUS2_PARSER_PARSER_OBJ=$(OBJ_DIR)/Sygus2Parser.tab.o
SYGUS2_PARSER_LEXER_OBJ=$(OBJ_DIR)/Sygus2Lexer.o

SYGUS2_PARSER_OBJS+=$(SYGUS2_PARSER_PARSER_OBJ)
SYGUS2_PARSER_OBJS+=$(SYGUS2_PARSER_LEXER_OBJ)

SYGUS2_PARSER_STATIC=$(SYGUS2_PARSER_ROOT)/lib/$(BUILD_SUFFIX)/libsygus2parser.a
SYGUS2_PARSER_DYNAMIC=$(SYGUS2_PARSER_ROOT)/lib/$(BUILD_SUFFIX)/libsygus2parser.so
SYGUS2_PARSER_TESTER=$(SYGUS2_PARSER_ROOT)/bin/$(BUILD_SUFFIX)/Sygus2Tester

default:			debug
debug:				all
opt:				all

all:				$(SYGUS2_PARSER_STATIC) $(SYGUS2_PARSER_DYNAMIC) # $(SYGUS2_PARSER_TESTER)

# $(SYGUS2_PARSER_DYNAMIC):		$(SYGUS2_PARSER_PARSER_OBJ) $(SYGUS2_PARSER_LEXER_OBJ) \
# 					$(SYGUS2_PARSER_DEPS) $(SYGUS2_PARSER_OBJS)
$(SYGUS2_PARSER_DYNAMIC):		$(SYGUS2_PARSER_DEPS) $(SYGUS2_PARSER_OBJS)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(LDPRINTNAME) `basename $@`"; \
		$(LD) $(OPTFLAGS) -shared -o $@ $(SYGUS2_PARSER_OBJS)
else
		$(LD) $(OPTFLAGS) -shared -o $@ $(SYGUS2_PARSER_OBJS)
endif

# $(SYGUS2_PARSER_STATIC):		$(SYGUS2_PARSER_PARSER_OBJ) $(SYGUS2_PARSER_LEXER_OBJ) \
# 					$(SYGUS2_PARSER_DEPS) $(SYGUS2_PARSER_OBJS)
$(SYGUS2_PARSER_STATIC):		$(SYGUS2_PARSER_DEPS) $(SYGUS2_PARSER_OBJS)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(ARPRINTNAME) `basename $@`"; \
		$(AR) $(ARFLAGS) $@ $(SYGUS2_PARSER_OBJS)
else
		$(AR) $(ARFLAGS) $@ $(SYGUS2_PARSER_OBJS)
endif

$(SYGUS2_PARSER_PARSER_GEN):	Sygus2Parser.y
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(BISONPRINTNAME) `basename $<` --> `basename $@`"; \
		$(BISON) -v --defines=$(SRC_DIR)/Sygus2Parser.tab.h -o $@ $<
else
		$(BISON) -v --defines=$(SRC_DIR)/Sygus2Parser.tab.h -o $@ $<
endif

$(SYGUS2_PARSER_LEXER_GEN): Sygus2Lexer.l
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(FLEXPRINTNAME) `basename $<` --> `basename $@`"; \
		$(FLEX) -o $@ $<
else
		$(FLEX) -o $@ $<
endif

$(SYGUS2_PARSER_PARSER_OBJ):	$(SYGUS2_PARSER_PARSER_GEN)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(CXXPRINTNAME) `basename $<` --> `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
endif

$(SYGUS2_PARSER_LEXER_OBJ):	$(SYGUS2_PARSER_LEXER_GEN) $(SYGUS2_PARSER_PARSER_GEN)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(CXXPRINTNAME) `basename $(SYGUS2_PARSER_LEXER_GEN)` --> `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) -c $< -o $@
endif

$(SYGUS2_PARSER_TESTER): $(SYGUS2_PARSER_TESTER_DEPS) $(SYGUS2_PARSER_TESTER_OBJS) $(SYGUS2_PARSER_STATIC)
ifeq "x$(VERBOSE_BUILD)" "x"
		@echo "$(LDPRINTNAME) `basename $@`"; \
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) $(SYGUS2_PARSER_TESTER_OBJS) -L $(SYGUS2_PARSER_ROOT)/lib/$(BUILD_SUFFIX) -Wl,-Bstatic -lsygus2parser -Wl,-Bdynamic -o $@
else
		$(CXX) $(CXXFLAGS) $(OPTFLAGS) $(SYGUS2_PARSER_TESTER_OBJS) -L $(SYGUS2_PARSER_ROOT)/lib/$(BUILD_SUFFIX) -Wl,-Bstatic -lsygus2parser -Wl,-Bdynamic -o $@
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
	rm -rf $(SYGUS2_PARSER_LEXER_GEN) $(SYGUS2_PARSER_PARSER_GEN) src/Sygus2Parser.tab.h src/Sygus2Parser.output

ifneq ($(MAKECMDGOALS), clean)
-include $(SYGUS2_PARSER_DEPS)
endif
