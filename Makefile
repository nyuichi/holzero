# Makefile
# 
# by Mark Adams
# Copyright (c) Proof Techonologies Ltd, 2012-2016

# This is the makefile for HOL Zero installation.  It should be run by executing
# "make" and then "make install" from the HOL Zero home directory, having
# specified the install options using "./configure".
#
# The main build stages are:
#  all       - Creates the executables in the HOL Zero 'etc' directory
#  install   - Installs the executables in the specified directory
#  clean     - Removes all temporary files used in the installation
#  uninstall - Removes the installed executables
#  distclean - Removes the temporary files, the installed executables and
#             Makefile.config
# 
# See Section 2 of etc/README for an explanation of the process for adjusting
# the lexical syntax of OCaml.


# Setup

.SILENT:

SHELL = /bin/bash -e

# Include Makefile.config if it exists
# This sets the following variables:
#   BUILD          - HOL Zero home directory
#   BIN            - Target directory for HOL Zero executables
#   OCAML_BIN      - Directory for OCaml executables
#   OCAML_LIB      - Directory for OCaml libraries
#   CAMLP5_BIN     - Directory for Camlp5 executables
#   CAMLP5_LIB     - Directory for Camlp5 libraries
#   OCAML_VERSION  - OCaml version
#   CAMLP5_VERSION - Camlp5 version
ifneq ($(wildcard Makefile.config),)
	include Makefile.config
	CAMLP5_MAJOR = `echo $(CAMLP5_VERSION) | sed -e 's/\..*//'`
endif


# User commands

.PHONY: all
all: print_header Makefile.config check_homedir check_bin_lib print_versions \
  etc/hzocaml etc/hzhelp etc/holzero
	echo ""
	echo "HOL Zero executables successfully built."
	echo "Now run \"make install\" to install executables."
	echo ""

.PHONY: install
install: print_header Makefile.config check_homedir \
  etc/hzocaml etc/hzhelp etc/holzero print_bindir
	if [ ! -d $(BIN) ]; then \
	  echo "Creating executables directory.."; \
	  mkdir -p $(BIN); \
	fi; \
	echo "Copying HOL Zero executables to executables directory.."; \
	cd $(BUILD)/etc; \
	cp -f hzhelp hzocaml holzero $(BIN); \
	cd $(BIN); \
	chmod a+x hzhelp hzocaml holzero; \
	echo ""; \
	echo "HOL Zero successfully installed."; \
	echo "Now run \"make clean\" to remove temporary files."; \
	cd $(BUILD); \
	if ( which holzero &> /dev/null ); then \
	  if [ ! "`which holzero`" = $(BIN)/holzero ]; then \
	    echo "WARNING: User execution path using wrong 'holzero'."; \
	    echo "See INSTALL Appendix III for details on how to adjust path.";\
	  fi; \
	else \
	  echo "WARNING: HOL Zero executables directory not in user execution \
	path."; \
	  echo "See INSTALL Appendix III for details on how to adjust path."; \
	fi; \
	echo ""

.PHONY: uninstall
uninstall: print_header Makefile.config check_homedir check_execdir print_bindir
	if [ -e $(BIN)/holzero ]; then \
	  echo "Removing 'holzero' executable.."; \
	  rm -f $(BIN)/holzero; \
	fi; \
	if [ -e $(BIN)/hzocaml ]; then \
	  echo "Removing 'hzocaml' executable.."; \
	  rm -f $(BIN)/hzocaml; \
	fi; \
	if [ -e $(BIN)/hzhelp ]; then \
	  echo "Removing 'hzhelp' executable.."; \
	  rm -f $(BIN)/hzhelp; \
	fi; \
	if [ $(BIN) = $(BUILD)/bin ] && \
	   [ -d $(BIN) ] && [ `ls -a $(BIN) | wc -l` = "2" ]; then \
	  echo "Removing executables directory.."; \
	  rmdir $(BIN); \
	fi
	echo ""; \
	echo "HOL Zero executables successfully uninstalled."; \
	echo ""

.PHONY: clean
clean: print_header Makefile.config check_homedir \
  clean0
	echo ""; \
	echo "Temporary installation files successfully removed."; \
	echo ""

.PHONY: distclean
distclean: print_header Makefile.config check_homedir print_bindir \
  clean0
	echo "Removing 'Makefile.config'.."; \
	rm -f $(BUILD)/Makefile.config; \
	echo ""; \
	echo "HOL Zero distribution fully cleansed."; \
	echo ""

.PHONY: clean0
clean0:
	echo "Removing temporary 'etc' files.."; \
	cd etc; \
	rm -f plexer_hz.ml plexer_hz.cmi plexer_hz.cmo plexer_hz.log \
	      pa_o_hz.ml pa_o_hz.cmi pa_o_hz.cmo pa_o_hz.log \
	      holzero hzhelp hzocaml


# Checks

.PHONY: check_homedir
check_homedir:
	if [ ! "`pwd`" = $(BUILD) ]; then \
          echo ""; \
	  echo "ERROR: Not in configured HOL Zero home directory:"; \
	  echo "         $(BUILD)"; \
	  echo "The HOL Zero home appears to have been copied or moved since \
configuration."; \
	  echo "Rerun \"./configure\" from current directory."; \
          echo ""; \
	  exit 1; \
	fi

.PHONY: check_bin_lib
check_bin_lib:
	if [ ! -e $(OCAML_BIN)/ocamlc ]; then \
          echo ""; \
	  echo "ERROR: Cannot find 'ocamlc' in configured location:"; \
	  echo "         $(OCAML_BIN)"; \
	  echo "Executable 'ocamlc' appears to have been moved or deleted \
since configuration."; \
	  echo "Rerun \"./configure\" or put back 'ocamlc'."; \
          echo ""; \
	  exit 1; \
	elif [ ! -e $(OCAML_BIN)/ocamlmktop ]; then \
          echo ""; \
	  echo "ERROR: Cannot find 'ocamlmktop' in configured location:"; \
	  echo "         $(OCAML_BIN)"; \
	  echo "Executable 'ocamlmktop' appears to have been moved or deleted \
since configuration."; \
	  echo "Rerun \"./configure\" or put back 'ocamlmktop'."; \
          echo ""; \
	  exit 1; \
	elif [ ! -e $(CAMLP5_BIN)/camlp5r ]; then \
          echo ""; \
	  echo "ERROR: Cannot find 'ocamlmktop' in configured location:"; \
	  echo "         $(CAMLP5_BIN)"; \
	  echo "Executable 'camlp5r' appears to have been moved or deleted \
since configuration."; \
	  echo "Rerun \"./configure\" or put back 'camlp5r'."; \
          echo ""; \
	  exit 1; \
	fi; \
	if [ ! -x $(OCAML_BIN)/ocamlc ]; then \
          echo ""; \
	  echo "ERROR: Cannot execute 'ocamlc' in configured location:"; \
	  echo "         $(OCAML_BIN)"; \
	  echo "Change its file permissions or change user."; \
          echo ""; \
	  exit 1; \
	elif [ ! -x $(OCAML_BIN)/ocamlmktop ]; then \
          echo ""; \
	  echo "ERROR: Cannot execute 'ocamlmktop' in configured location:"; \
	  echo "         $(OCAML_BIN)"; \
	  echo "Change its file permissions or change user."; \
          echo ""; \
	  exit 1; \
	elif [ ! -x $(CAMLP5_BIN)/camlp5r ]; then \
          echo ""; \
	  echo "ERROR: Cannot execute 'camlp5r' in configured location:"; \
	  echo "         $(OCAML_BIN)"; \
	  echo "Change its file permissions or change user."; \
          echo ""; \
	  exit 1; \
	fi

.PHONY: check_execdir
check_execdir: Makefile.config
	if [ ! -d $(BIN) ]; then \
	  echo ""; \
	  echo "ERROR: Missing executables directory: $(BIN)."; \
          echo ""; \
	  exit 1; \
	fi

.PHONY: print_header
print_header:
	echo ""; \
	echo "HOL ZERO MAKE"

.PHONY: print_bindir
print_bindir:
	echo "Using executables directory:"; \
	echo "  $(BIN)"; \

.PHONY: print_versions
print_versions:
	echo "Using OCaml version: $(OCAML_VERSION)"; \
	echo "Using Camlp5 version: $(CAMLP5_VERSION)";


# Error for when missing 'Makefile.config'

Makefile.config:
	echo ""; \
	echo "ERROR: Missing 'Makefile.config' in HOL Zero home directory."; \
	echo "Run \"./configure\" before running \"make\"."; \
	echo ""; \
	exit 1;


# Creating bytecode for adjusting the OCaml lexical syntax

etc/plexer_hz.ml etc/pa_o_hz.ml: Makefile.config
	echo "Creating 'plexer_hz.ml' and 'pa_o_hz.ml'.."
	cp etc/plexer_hz.$(CAMLP5_MAJOR).ml etc/plexer_hz.ml; \
	cp etc/pa_o_hz.$(CAMLP5_MAJOR).ml etc/pa_o_hz.ml

etc/plexer_hz.cmo: Makefile.config etc/plexer_hz.ml
	echo "Creating 'plexer_hz.cmo'.."; \
	cd etc; \
	$(OCAML_BIN)/ocamlc \
	    -c \
	    -pp "$(CAMLP5_BIN)/camlp5r pa_lexer.cmo" \
	    -I "$(CAMLP5_LIB)" \
	    plexer_hz.ml   &> plexer_hz.log; \
	if [ ! -e plexer_hz.cmo ]; then \
	  echo ""; \
	  echo "ERROR: Creation of 'plexer_hz.cmo' fails."; \
	  echo "See 'etc/plexer_hz.log' for details."; \
          echo ""; \
	  exit 1; \
	fi

etc/pa_o_hz.cmo: etc/pa_o_hz.ml
	echo "Creating 'pa_o_hz.cmo'.."; \
	cd etc; \
	$(OCAML_BIN)/ocamlc \
	    -c \
	    -pp "$(CAMLP5_BIN)/camlp5r pa_extend.cmo q_MLast.cmo" \
	    -I "$(CAMLP5_LIB)" \
	    pa_o_hz.ml   &> pa_o_hz.log; \
	if [ ! -e pa_o_hz.cmo ]; then \
	  echo ""; \
	  echo "ERROR: Creation of 'pa_o_hz.cmo' fails."; \
	  echo "See 'etc/pa_o_hz.log' for details."; \
          echo ""; \
	  exit 1; \
	fi


# Putting together the executables

etc/hzocaml: etc/plexer_hz.cmo etc/pa_o_hz.cmo
	echo "Creating 'hzocaml'.."; \
	$(OCAML_BIN)/ocamlmktop \
	    -o etc/hzocaml \
	    nums.cma $(CAMLP5_LIB)/camlp5o.cma \
	    etc/plexer_hz.cmo etc/pa_o_hz.cmo

etc/hzhelp:
	echo "Creating 'hzhelp'.."; \
	cat etc/hzhelp.header                                  > etc/hzhelp; \
	echo "# Configured settings (automatically generated)" >>etc/hzhelp; \
	echo "# Created on `date +\"%a %d %b %T %Z %Y\"`."     >>etc/hzhelp; \
	echo ""                                                >>etc/hzhelp; \
	echo "BUILD=\"$(BUILD)\""                              >>etc/hzhelp; \
	cat etc/hzhelp.main                                    >>etc/hzhelp

etc/holzero: etc/hzocaml
	echo "Creating 'holzero'.."; \
	cat etc/holzero.header                                 > etc/holzero; \
	echo "# Configured settings (automatically generated)" >>etc/holzero; \
	echo "# Created on `date +\"%a %d %b %T %Z %Y\"`."     >>etc/holzero; \
	echo ""                                                >>etc/holzero; \
	echo "BIN=\"$(BIN)\""                                  >>etc/holzero; \
	echo "BUILD=\"$(BUILD)\""                              >>etc/holzero; \
	echo "CAMLP5_LIB=\"$(CAMLP5_LIB)\""                    >>etc/holzero; \
	cat etc/holzero.main                                   >>etc/holzero
