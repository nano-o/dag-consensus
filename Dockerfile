FROM debian:stable-slim

RUN apt-get update && apt-get install -y \
    openjdk-17-jre \
    make sudo aptitude wget \
    && rm -rf /var/lib/apt/lists/*

RUN apt-get update && apt-get install -y \
    texlive \
    && rm -rf /var/lib/apt/lists/*

RUN apt-get update && apt-get install -y \
    vim nano \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m -s /bin/bash appuser && \
    echo "appuser ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/appuser && \
    chmod 0440 /etc/sudoers.d/appuser

# Set the working directory inside the container
WORKDIR /app

COPY *.tla *.cfg Makefile README* tla2tools.jar /app/

# Change ownership to the non-root user
RUN chown -R appuser:appuser /app

# Switch to non-root user
USER appuser

# Default command is to start a shell interactively
CMD ["/bin/bash"]

# To build and save:
#   docker build . -t giulianolosa/sbc25
#   docker save -o sbc25.tar giulianolosa/sbc25:latest
#   gzip sbc25.tar

