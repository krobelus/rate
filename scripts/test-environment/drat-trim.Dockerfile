FROM circleci/buildpack-deps:buster
USER root

RUN set -eux; \
    git clone https://github.com/marijnheule/drat-trim; \
    cd drat-trim; \
    make; \
    cp drat-trim /usr/local/bin/; \
    git clone https://github.com/marijnheule/dpr-trim; \
    cd dpr-trim; \
    make; \
    gcc dpr-trim.c -O2 -o dpr-trim; \
    cp dpr-trim /usr/local/bin/;
