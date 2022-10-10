OCAMLBUILD = ocamlbuild

# OPAM repository
OPREP = $(OCAML_TOPLEVEL_PATH)/..
ELIB = extlib/extLib
GRLIB = ocamlgraph/graph
OLIBS = $(OPREP)/$(GRLIB),
CPPO_FLAGS =

ifdef OCAML_TOPLEVEL_PATH
 INCLPRE = $(OPREP)
 LIBELIB = $(OPREP)/$(ELIB)
 LIBGLIB = $(OPREP)/$(GRLIB)
 LIBIGRAPH = $(OPREP)/ocamlgraph
else
 INCLPRE = +site-lib
 LIBELIB = $(ELIB)
 LIBGLIB = graph
 LIBIGRAPH = +ocamlgraph
endif

#  number of parallel jobs, 0 means unlimited.
JOBS = 16

# dynlink should precede camlp4lib
LIBSB = unix,str,dynlink,camlp4lib,nums,$(LIBELIB),$(LIBGLIB)
LIBSN = unix,str,dynlink,camlp4lib,nums,$(LIBELIB),$(LIBGLIB)
#,z3
LIBS2 = unix,str,dynlink,camlp4lib
#-I,+lablgtk2,
INCLUDES = -I,+src/smtlib,-I,+src/kil,-I,+src/kparser,-I,+src/core,-I,+src/util,-I,+src/fixpoint,-I,+src/backend,-I,+src/type,-I,+camlp4,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH)
INCLUDESN = -I,+src/smtlib,-I,+src/kil,-I,+src/kparser,-I,+src/core,-I,+src/util,-I,+src/fixpoint,-I,+src/backend,-I,+src/type,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH)

PROPERERRS = -warn-error,+4+8+9+11+12+25+28

FLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-fopenmp

GFLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp
SCFLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-fopenmp
SLFLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-static,-ccopt,-fopenmp

# -no-hygiene flag to disable "hygiene" rules
OBB_GFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)  $(CPPO_FLAGS)
OBB_NGFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)

OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)

#static - incl C libs
OBNS_FLAGS = -no-links -libs $(LIBSN) -cflags $(SCFLAGS) -lflags $(SLFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) $(CPPO_FLAGS)


all: byte

byte: ksolver.byte


native: ksolver.native
static: ksolver.native

ksat: ksolver.native


ksolver.byte:
	 @ocamlbuild $(OBB_FLAGS) ksolver.byte
	cp -u _build/src/ksolver.byte bin/ksolver
	cp -u _build/src/ksolver.byte bin/b-ksolver
	cp -u _build/src/ksolver.byte release/bin/ksolver

ksolver.native:
	@ocamlbuild $(OBN_FLAGS) ksolver.native
	cp -u _build/src/ksolver.native bin/ksolver
	cp -u _build/src/ksolver.native bin/n-ksolver
	cp -u _build/src/ksolver.native release/bin/ksolver

sksolver.native:
	@ocamlbuild $(OBNS_FLAGS) ksolver.native
	cp -u _build/src/ksolver.native bin/ksolver
	cp -u _build/src/ksolver.native bin/s-ksolver

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f bin/ksolver bin/ksolver.norm bin/ksolver.byte
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot *.depends


install-native: ksat.native
	cp -u _build/ksat.native /usr/local/bin/ksat
