# Use a slim Python base
FROM python:3.11-slim

# System deps for Geo stack
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      gdal-bin libgdal-dev proj-bin libspatialindex-dev \      build-essential curl && \    rm -rf /var/lib/apt/lists/*

# Hints for GDAL/PROJ; harmless if unused
ENV CPLUS_INCLUDE_PATH=/usr/include/gdal
ENV C_INCLUDE_PATH=/usr/include/gdal

# Workdir
WORKDIR /app

# Install Python deps first (better cache)
COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

# Copy your app
COPY python_deploy.py /app/python_deploy.py
# Copy data folder (place shapefiles here)
COPY data/ /app/data/

# Runtime settings
ENV HEADLESS=1
ENV ROADS_SHAPEFILE=/app/data/roads.shp
ENV TRANSIT_STOPS_SHAPEFILE=/app/data/transit_stops.shp
# Railway/Render often inject PORT; your script can read it.
ENV PORT=8000

EXPOSE 8000

# Start your existing server
CMD ["python", "-u", "python_deploy.py"]
