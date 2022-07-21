# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS ?=
DUNE     := dune
NAME     := coq-mathcomp-quantum
DISTDIR  := $(NAME)
SED      := sed
TAR      := tar
REPO     := default=https://opam.ocaml.org,coq-released=https://coq.inria.fr/opam/released

# --------------------------------------------------------------------
.PHONY: default build build-local opam clean mrproper dist distcheck

default: build

build:
	$(DUNE) build $(DUNEOPTS)

build-local: opam
	opam config exec -- $(DUNE) build --root=. $(DUNEOPTS)

opam:
	[ -d _opam ] || opam switch create --yes --deps-only --repositories=$(REPO) .

clean:
	$(DUNE) clean

mrproper: clean
	rm -rf _opam

dist:
	rm -rf $(DISTDIR) $(NAME).tar.gz
	./scripts/distribution $(DISTDIR) MANIFEST
	$(TAR) -czf $(NAME).tar.gz --owner=0 --group=0 $(DISTDIR)
	rm -rf $(DISTDIR)

distcheck: dist
	$(TAR) -xof $(NAME).tar.gz
	set -x; \
       $(MAKE) -C $(DISTDIR) build-local \
    && $(MAKE) -C $(DISTDIR) dist \
    && mkdir $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
    && ( cd $(DISTDIR)/dist1 && tar -xof ../$(NAME).tar.gz ) \
    && ( cd $(DISTDIR)/dist2 && tar -xof ../../$(NAME).tar.gz ) \
    && diff -rq $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
    || exit 1
	rm -rf $(DISTDIR)
	@echo "$(DISTDIR) is ready for distribution" | \
    $(SED) -e 1h -e 1s/./=/g -e 1p -e 1x -e '$$p' -e '$$x'
