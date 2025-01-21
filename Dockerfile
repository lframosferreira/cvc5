FROM ubuntu:latest

# Set environment variables to suppress interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive
ENV CXXFLAGS="-w" 
ENV CFLAGS="-w"

ENV WERROR=0
ENV WARNINGS_AS_ERRORS=0


RUN apt-get update
RUN apt-get install -y git build-essential vim cmake libtool autoconf automake python3 python3-pip python3-venv curl sudo software-properties-common make libgmp-dev libhwloc-dev pkg-config

# Clone and build mata
RUN git clone https://github.com/VeriFIT/mata.git
RUN cd mata && make release
RUN cd mata && sudo make install

# Clone and build cvc5
RUN git clone https://github.com/lframosferreira/cvc5.git
RUN cd cvc5 && git checkout automata_based_lia_solver
RUN cd cvc5 && bash configure.sh --mata --auto-download
RUN cd cvc5/build && make -j8
RUN cd cvc5/build && make check
RUN cd cvc5/build && sudo make install

# Build amaya
RUN git clone https://github.com/trolando/sylvan.git sylvan
RUN mkdir -p sylvan/build
RUN cd sylvan && git checkout v1.5.0
RUN cd sylvan && sed -i 's/-Werror//g' CMakeLists.txt
RUN cd sylvan/build && cmake ..
RUN cd sylvan/build && make -j`nproc`
RUN cd sylvan/build && make install

RUN git clone https://github.com/MichalHe/amaya-mtbdd.git amaya-mtbdd
RUN cd amaya-mtbdd && make -j`nproc` shared-lib

RUN git clone https://github.com/MichalHe/amaya.git 
RUN cd amaya && cp ../amaya-mtbdd/build/amaya-mtbdd.so /amaya/
RUN cd amaya && pip3 install -r requirements.txt --break-system-packages
ENV LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:/usr/local/lib/"

# Default command to keep the container running
CMD ["/bin/bash"]

