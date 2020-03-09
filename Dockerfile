FROM ubuntu:18.04

RUN apt-get update && apt-get install --no-install-recommends -y make perl vim polyml libpolyml-dev

USER root
ENV WDIR /home/root/RPx
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}
ADD . ${WDIR}
RUN chmod +x scripts/*
RUN make init && make polyml && cp bin/polyml/rpxprover /usr/bin/rpxprover