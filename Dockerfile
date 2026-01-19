FROM debian:stable-slim

RUN apt-get update && apt-get install -y \
    default-jre-headless \
    make sudo aptitude wget ca-certificates \
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
#   docker build . -t giulianolosa/ccs2025-artifact
#   docker save -o ccs2025-docker-image.tar giulianolosa/ccs2025-artifact:latest
#   gzip ccs2025-docker-image.tar
