FROM circleci/buildpack-deps:buster
USER root

RUN set -eux; \
    git clone https://github.com/marijnheule/drat-trim; \
    cd drat-trim; \
    git checkout 59d345a04ec0fe1694e2fef87ef7698a826683d8; \
    make; \
    curl -O https://www.cs.utexas.edu/~marijn/pr/dpr-trim.c; \
    gcc dpr-trim.c -O2 -o dpr-trim; \
    cp drat-trim dpr-trim /usr/local/bin/;


