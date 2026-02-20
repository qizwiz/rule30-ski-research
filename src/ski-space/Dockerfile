FROM ubuntu:24.04

# Install SBCL + Python
RUN apt-get update && apt-get install -y --no-install-recommends \
    sbcl \
    python3 \
    python3-pip \
    python3-venv \
    && rm -rf /var/lib/apt/lists/*

# Python deps
RUN pip3 install --break-system-packages gradio pandas

WORKDIR /app
COPY . .

# Persistent storage mount point (HF mounts /data for paid tiers)
RUN mkdir -p /data/ski-meta

ENV PYTHONUNBUFFERED=1
ENV STATE_DIR=/data/ski-meta

EXPOSE 7860

CMD ["python3", "app.py"]
