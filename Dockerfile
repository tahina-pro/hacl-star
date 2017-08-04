FROM ubuntu:xenial

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>
# Based on the original F* formula with Daniel Fabian

# Define versions of dependencies
ENV opamv 4.04.2
ENV z3v z3-4.5.0

# Install required packages and set versions
RUN apt-get -qq update
RUN apt-get install --yes sudo libssl-dev libsqlite3-dev g++-5 gcc-5 m4 make opam pkg-config python libgmp3-dev cmake
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200
RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200

# Create user
RUN useradd -ms /bin/bash Work
RUN echo "Work ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER Work
WORKDIR /home/Work

# Prepare build (OCaml packages)
ENV OPAMYES true
RUN opam init
RUN echo ". /home/Work/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true" >> .bashrc
RUN opam switch ${opamv}
RUN opam install ocamlfind batteries sqlite3 fileutils yojson ppx_deriving_yojson zarith pprint menhir ulex process fix wasm stdint

# Prepare and build Z3
RUN git clone -b ${z3v} https://github.com/Z3Prover/z3.git
WORKDIR z3
RUN python scripts/mk_make.py
WORKDIR build
RUN make
RUN sudo make install
WORKDIR /home/Work

# Prepare and build F*
RUN git clone https://github.com/FStarLang/FStar.git
WORKDIR /home/Work/FStar
RUN git checkout 376a7b279fd1656d1b9890b1582a29f02514a19a
ENV PATH "~/FStar/bin:$PATH"
RUN opam config exec -- make -C src/ocaml-output
WORKDIR /home/Work

# Prepare and build KreMLin
RUN git clone https://github.com/FStarLang/kremlin.git
WORKDIR /home/Work/kremlin
RUN git checkout f3a8fbf58a713ab5548902e5272bd9dd66688630
ENV PATH "~/kremlin:$PATH"
RUN opam config exec -- make
WORKDIR /home/Work

# Prepare and build HaCl*
RUN git clone https://github.com/mitls/hacl-star.git
WORKDIR /home/Work/hacl-star
RUN git checkout mozilla
ENV FSTAR_HOME /home/Work/FStar
ENV KREMLIN_HOME /home/Work/kremlin
ENV FSTAR_HOME /home/Work/hacl-star

# Run extraction for Curve25519
RUN opam config exec -- make -C code/curve25519 extract-c

# Produce artifacts for NSS
WORKDIR /home/Work
RUN mkdir artifacts
RUN cp hacl-star/snapshots/nss/kremlib.h artifacts
RUN cp hacl-star/code/curve25519-c/* artifacts