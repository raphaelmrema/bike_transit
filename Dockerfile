# Clean Dockerfile for GeoPython
FROM python:3.11-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    gdal-bin \
    libgdal-dev \
    proj-bin \
    proj-data \
    libspatialindex-dev \
    libgeos-dev \
    build-essential \
    curl \
    ca-certificates \
 && rm -rf /var/lib/apt/lists/*

ENV CPLUS_INCLUDE_PATH=/usr/include/gdal
ENV C_INCLUDE_PATH=/usr/include/gdal

WORKDIR /app

COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

COPY python_deploy.py /app/python_deploy.py
COPY data/ /app/data/

ENV HEADLESS=1
ENV ROADS_SHAPEFILE=/app/data/roads.shp
ENV TRANSIT_STOPS_SHAPEFILE=/app/data/transit_stops.shp
ENV PORT=8000

EXPOSE 8000

CMD ["python", "-u", "python_deploy.py"]
