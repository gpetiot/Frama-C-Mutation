
FRAMAC_SHARE	:=$(shell frama-c.byte -print-path)
FRAMAC_LIBDIR	:=$(shell frama-c.byte -print-libpath)
PLUGIN_NAME	:= Mutation

PLUGIN_TESTS_DIRS := search

PLUGIN_CMO	:= options register
include $(FRAMAC_SHARE)/Makefile.dynamic

clean::
	$(RM) mutant_*.c
