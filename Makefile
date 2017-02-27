#
# Main HACL* Makefile
#

verify:
	$(MAKE) -C test verify


extract-c:
	$(MAKE) -C test extract-c-code
	$(MAKE) -C test build-snapshot

run-c:
	$(MAKE) -C test test-snapshot

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	$(MAKE) -C test clean

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
