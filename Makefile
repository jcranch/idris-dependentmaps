runtests:
	$(IDRIS_PACK_HOME)/bin/spec-discover test
	pack test dependentmaps

compile:
	pack build
