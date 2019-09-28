#!/bin/sh

set -eu

cd "$(dirname "$0")"/test-environment

docker login --password-stdin

for image in drat-trim grat rupee rate-test-environment; do
    echo $image
    docker pull krobelus/$image ||:
    docker build -t krobelus/$image -f $image.Dockerfile .
    docker push krobelus/$image
done

docker logout
