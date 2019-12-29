# dep drat-trim
# dep grat
# dep rupee

FROM circleci/rust:1.37-buster
USER root

COPY --from=jixone/rust-ci:check-lrat \
	/acl2-8.1/books/projects/sat/lrat/stobj-based \
	/usr/local/lib/stobj-based

COPY --from=jixone/rust-ci:check-lrat \
	/acl2-8.1/books/projects/sat/lrat/incremental \
	/usr/local/lib/incremental

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/bin/check-lrat \
        /usr/local/bin/check-lrat

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/bin/check-clrat \
        /usr/local/bin/check-clrat

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/bin/check-lrat.core \
        /usr/local/bin/check-lrat.core

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/bin/check-clrat.core \
        /usr/local/bin/check-clrat.core

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/bin/sbcl \
        /usr/local/bin/sbcl

COPY --from=jixone/rust-ci:check-lrat \
        /usr/local/lib/sbcl \
        /usr/local/lib/sbcl

COPY lrat-check /usr/local/bin/lrat-check
COPY lrat-check /usr/local/bin/clrat-check
RUN sed -i -e 's/stobj-based/incremental/' -e 's/check-lrat/check-clrat/' /usr/local/bin/clrat-check

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

USER circleci
