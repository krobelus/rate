FROM circleci/buildpack-deps:buster
USER root

COPY rupee-fix-reviseWatches.patch .

RUN set -eux; \
	git clone https://github.com/arpj-rebola/rupee; \
	cd rupee; \
	git checkout b00351cbd3173d329ea183e08c3283c6d86d18a1; \
	git apply < ../rupee-fix-reviseWatches.patch; \
	make; \
	cp bin/rupee /usr/local/bin;
