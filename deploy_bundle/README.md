# Web Deployment Bundle for Your Python GIS Tool

This repository contains the minimal files you need to containerize and deploy your existing `python_deploy.py` to the web (Railway/Render/Fly.io/VPS).

## Files included
- `Dockerfile` — builds a container image with GDAL/GEOS/PROJ and your Python stack.
- `requirements.txt` — Python dependencies used by your tool and optional FastAPI/UVicorn.
- `.gitignore` & `.dockerignore` — keep images lean and your repo clean.
- `env.example` — example environment variables for local `.env` or platform secrets.
- `data/.gitkeep` — placeholder; put your shapefiles here.

> Your `python_deploy.py` is **not** modified here. Two tiny OPTIONAL edits are recommended so it runs flawlessly on platforms that assign a `PORT` and run headless browsers.

### Optional edits to `python_deploy.py`
```python
import os
# Prefer platform port if supplied
port_from_env = os.getenv("PORT")
if port_from_env:
    PORT = int(port_from_env)

# Use env for input paths & secrets
ROADS_SHAPEFILE = os.getenv("ROADS_SHAPEFILE", "/app/data/roads.shp")
TRANSIT_STOPS_SHAPEFILE = os.getenv("TRANSIT_STOPS_SHAPEFILE", "/app/data/transit_stops.shp")
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")

# Avoid auto-opening a browser in containers
HEADLESS = os.getenv("HEADLESS", "1") == "1"
if not HEADLESS:
    # keep your existing webbrowser.open(...) logic here
    pass
```

## Put your data
Place the full shapefile components in `data/`:
```
data/
  roads.shp  roads.dbf  roads.shx  roads.prj
  transit_stops.shp  transit_stops.dbf  transit_stops.shx  transit_stops.prj
```

## Build & run locally (optional)
```bash
docker build -t bike-gis-tool .
docker run --rm -p 8000:8000 \
  -e GOOGLE_API_KEY=your_key \
  -e HEADLESS=1 \
  bike-gis-tool
```

## Deploy with Railway
1. Create a new GitHub repo and push these files + your `python_deploy.py` and `data/` (or add data later).
2. On Railway: **New Project → Deploy from GitHub** and select the repo.
3. Set environment variables in **Variables**:
   - `GOOGLE_API_KEY` = your key
   - `HEADLESS` = `1`
   - (optional) `ROADS_SHAPEFILE`, `TRANSIT_STOPS_SHAPEFILE` if paths differ
4. Open the generated URL when the build finishes.

## Troubleshooting
- **Port issues**: Ensure your script binds to `0.0.0.0` and (optionally) reads the `PORT` env var.
- **GDAL/Fiona errors**: Rebuild; first-time builds are heavy. Confirm shapefile paths exist inside the container (`/app/data/...`).
- **No browser**: Containers are headless by default; interact via the web URL printed in logs or provided by the platform.
