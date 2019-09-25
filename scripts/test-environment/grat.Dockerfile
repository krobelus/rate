FROM circleci/buildpack-deps:buster
USER root

RUN set -eux; \
	apt-get install cmake libboost-timer-dev; \
	curl -O http://www21.in.tum.de/~lammich/grat/gratgen.tgz; \
	tar xf gratgen.tgz; \
	mkdir -p gratgen/build; \
	cd gratgen/build; \
	cmake ..; \
	make; \
	cp gratgen /usr/local/bin/;

RUN set -eux; \
	echo  'deb http://deb.debian.org/debian	stretch	main' >> /etc/apt/sources.list;	\
	apt-get update; apt	install	mlton; \
	curl -O	http://www21.in.tum.de/~lammich/grat/gratchk.tgz; \
	tar xf gratchk.tgz; \
	cd gratchk/code; \
	make; \
	cp gratchk /usr/local/bin;
