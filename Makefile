runtests:
	spec-discover test/
	pack test dependentmaps

compile:
	pack build
