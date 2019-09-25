# dep drat-trim
# dep grat
# dep rupee

FROM circleci/rust:1.37-buster
USER root

COPY --from=jixone/rust-ci:check-lrat \
	/acl2-8.1/books/projects/sat/lrat/stobj-based/ \
	/acl2-8.1/books/projects/sat/lrat/incremental/ \
	/usr/local/lib/

COPY lrat-check /usr/local/bin/lrat-check
COPY lrat-check /usr/local/bin/clrat-check
RUN sed -i 's/stobj-based/incremental/' /usr/local/bin/clrat-check

COPY --from=krobelus/drat-trim \
	/usr/local/bin/drat-trim \
	/usr/local/bin/dpr-trim \
	/usr/local/bin/

COPY --from=krobelus/grat \
	/usr/local/bin/gratgen \
	/usr/local/bin/gratchk \
	/usr/local/bin/

COPY --from=krobelus/rupee \
	/usr/local/bin/rupee \
	/usr/local/bin/

RUN apt-get install python3-pytest

USER circleci
