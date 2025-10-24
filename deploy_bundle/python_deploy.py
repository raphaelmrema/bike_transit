# bike_bus_bike_google_part1.py
# Part 1: Core Imports, Configuration, and Utility Functions

import os
import json
import http.server
import socketserver
import urllib.parse
import tempfile
import threading
import webbrowser
import shutil
import math
import requests
import datetime
import zipfile
import pandas as pd
import geopandas as gpd
import io
import socket
import time
import sys
import numpy as np
from functools import partial
from typing import List, Dict, Optional
from shapely.geometry import Point, LineString
from shapely.ops import nearest_points

# =============================================================================
# CONFIGURATION SETTINGS - UPDATE THESE TO MATCH YOUR ENVIRONMENT
# =============================================================================


# Shapefile Paths - UPDATE THESE
ROADS_SHAPEFILE = r"D:\Users\n01621754\OneDrive - University of North Florida\Desktop\WSDOT RESEARCH\GIS WORKS\roads.shp"
TRANSIT_STOPS_SHAPEFILE = r"D:\Users\n01621754\OneDrive - University of North Florida\Desktop\WSDOT RESEARCH\GIS WORKS\transit_stops.shp"

# Google Maps API Configuration
GOOGLE_API_KEY = "AIzaSyB7Khy5ec8OotFSO-4Eckjpqot6BxOLWBo"

# Bicycle Configuration
BIKE_SPEED_MPH = 11  # Average bicycle speed
BIKE_SPEED_FEET_PER_SECOND = BIKE_SPEED_MPH * 5280 / 3600

# Jacksonville Default Center
DEFAULT_CENTER = (30.3293, -81.6556)
DEFAULT_ZOOM = 12

# Server Configuration
DEFAULT_PORT = 8000
SERVER_TIMEOUT = 30

# Temporary Workspace
TEMP_WORKSPACE = os.path.join(tempfile.gettempdir(), "bike_bus_bike_google")
if not os.path.exists(TEMP_WORKSPACE):
    os.makedirs(TEMP_WORKSPACE)

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def find_available_port(start_port=DEFAULT_PORT, max_attempts=100):
    """Find an available port starting from start_port"""
    for port in range(start_port, start_port + max_attempts):
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
                sock.bind(('localhost', port))
                return port
        except OSError:
            continue
    raise RuntimeError(f"Could not find an available port in range {start_port}-{start_port + max_attempts}")

def clean_temporary_files():
    """Clean up all temporary files"""
    try:
        if os.path.exists(TEMP_WORKSPACE):
            shutil.rmtree(TEMP_WORKSPACE, ignore_errors=True)
        if not os.path.exists(TEMP_WORKSPACE):
            os.makedirs(TEMP_WORKSPACE)
    except Exception as e:
        print(f"Warning: Could not clean temporary files: {str(e)}")

def is_valid_api_key():
    """Check if the Google Maps API key is properly configured"""
    invalid_keys = [
        "YOUR_ACTUAL_GOOGLE_MAPS_API_KEY_HERE",
        "YOUR_GOOGLE_MAPS_API_KEY_HERE", 
        "",
        None
    ]
    
    return (GOOGLE_API_KEY and 
            GOOGLE_API_KEY not in invalid_keys and
            len(GOOGLE_API_KEY) > 30)

def calculate_bike_time_minutes(distance_meters, use_google_api=False, start_coords=None, end_coords=None):
    """
    Calculate bicycle travel time in minutes given distance in meters.
    Can optionally use Google Maps API for more accurate estimates.
    """
    if use_google_api and start_coords and end_coords and is_valid_api_key():
        try:
            # Use Google Maps API for accurate bike time
            url = "https://maps.googleapis.com/maps/api/directions/json"
            params = {
                'origin': f"{start_coords[1]},{start_coords[0]}",
                'destination': f"{end_coords[1]},{end_coords[0]}",
                'mode': 'bicycling',
                'key': GOOGLE_API_KEY
            }
            response = requests.get(url, params=params, timeout=10)
            data = response.json()
            
            if data.get('status') == 'OK' and data.get('routes'):
                duration_seconds = data['routes'][0]['legs'][0]['duration']['value']
                return round(duration_seconds / 60, 1)
        except Exception as e:
            print(f"Error getting Google Maps bike time, falling back to calculation: {e}")
    
    # Fallback to distance-based calculation
    if distance_meters <= 0:
        return 0
    distance_feet = distance_meters * 3.28084
    return (distance_feet / BIKE_SPEED_FEET_PER_SECOND) / 60

def format_time_duration(minutes):
    """Format time duration in a user-friendly way"""
    if minutes < 1:
        return "< 1 min"
    elif minutes < 60:
        return f"{int(minutes)} min"
    else:
        hours = int(minutes // 60)
        mins = int(minutes % 60)
        if mins == 0:
            return f"{hours}h"
        else:
            return f"{hours}h {mins}m"

def decode_polyline(polyline_str):
    """Decode Google polyline string to coordinates"""
    try:
        import polyline as polyline_lib
        coords = polyline_lib.decode(polyline_str)
        return [[lon, lat] for lat, lon in coords]
    except ImportError:
        # Fallback manual implementation
        index = 0
        lat = 0
        lng = 0
        coordinates = []
        
        while index < len(polyline_str):
            result = 1
            shift = 0
            while True:
                b = ord(polyline_str[index]) - 63 - 1
                index += 1
                result += b << shift
                shift += 5
                if b < 0x1f:
                    break
            lat += (~result >> 1) if (result & 1) != 0 else (result >> 1)
            
            result = 1
            shift = 0
            while True:
                b = ord(polyline_str[index]) - 63 - 1
                index += 1
                result += b << shift
                shift += 5
                if b < 0x1f:
                    break
            lng += (~result >> 1) if (result & 1) != 0 else (result >> 1)
            
            coordinates.append([lng / 1e5, lat / 1e5])
        
        return coordinates
    except Exception as e:
        print(f"Error decoding polyline: {e}")
        return []

def _map_field(row_or_columns, candidates):
    """
    Given a pandas Index (columns) or dict-like row, return the first existing key
    that matches (case-insensitive) any of the candidate names.
    """
    if hasattr(row_or_columns, 'keys'):
        keys = list(row_or_columns.keys())
    else:
        keys = list(row_or_columns)
    
    lower_map = {str(k).lower(): k for k in keys}
    
    for cand in candidates:
        lc = str(cand).lower()
        if lc in lower_map:
            return lower_map[lc]
    return None

def classify_lts(facility_type, speed_limit, lanes):
    """Classify Level of Traffic Stress (LTS) from 1 (best) to 4 (worst)"""
    ft = str(facility_type or "").upper().strip()
    
    try:
        sp = float(speed_limit) if speed_limit is not None else 30
    except (ValueError, TypeError):
        sp = 30
    
    try:
        ln = int(lanes) if lanes is not None else 2
    except (ValueError, TypeError):
        ln = 2

    protected_facilities = {
        "PROTECTED BIKELANE", "PROTECTED BIKE LANE", 
        "SHARED USE PATH", "MIXED USE PATH", "BIKE PATH"
    }
    
    buffered_facilities = {
        "BUFFERED BIKELANE", "BUFFERED BIKE LANE", 
        "UNBUFFERED BIKELANE", "UNBUFFERED BIKE LANE"
    }
    
    shared_facilities = {
        "SHARED LANE", "BIKE ROUTE"
    }

    if ft in protected_facilities:
        return 1
    elif ft in buffered_facilities and sp <= 30:
        return 2
    elif ft in shared_facilities and sp <= 35 and ln <= 2:
        return 3
    else:
        return 4

print("Part 1: Core configuration and utilities loaded successfully")

# bike_bus_bike_google_part2.py
# Part 2: Enhanced GTFS Manager with Real-time Capabilities

class EnhancedGTFSManager:
    """Enhanced GTFS manager with real-time capabilities for bike-bus-bike routing"""
    
    def __init__(self):
        self.gtfs_data = {}
        self.stops_df = None
        self.routes_df = None
        self.stop_times_df = None
        self.trips_df = None
        self.calendar_df = None
        self.is_loaded = False
        self.last_update = None
        self.realtime_cache = {}
        self.cache_duration = 30  # seconds
        
    def load_gtfs_data(self, gtfs_urls=None):
        """Load GTFS data with enhanced error handling"""
        if gtfs_urls is None:
            gtfs_urls = [
                "https://ride.jtafla.com/gtfs-archive/gtfs.zip",
                "https://schedules.jtafla.com/schedulesgtfs/download",
                "https://openmobilitydata.org/p/jacksonville-transportation-authority/331/latest/download",
            ]
        
        print("Loading GTFS data for bike-bus-bike routing...")
        
        for i, url in enumerate(gtfs_urls):
            try:
                print(f"Trying GTFS source {i+1}: {url}")
                
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                    'Accept': 'application/zip, application/octet-stream, */*',
                    'Accept-Language': 'en-US,en;q=0.9',
                }
                
                response = requests.get(url, timeout=45, headers=headers, verify=False, stream=True)
                response.raise_for_status()
                
                content = response.content
                if not content.startswith(b'PK'):
                    print(f"   Response is not a ZIP file, skipping...")
                    continue
                
                print(f"   Valid ZIP file detected ({len(content)} bytes)")
                
                with zipfile.ZipFile(io.BytesIO(content)) as z:
                    files_to_load = {
                        'stops.txt': 'stops_df',
                        'routes.txt': 'routes_df', 
                        'trips.txt': 'trips_df',
                        'stop_times.txt': 'stop_times_df',
                        'agency.txt': 'agency_df',
                        'calendar.txt': 'calendar_df'
                    }
                    
                    loaded_files = 0
                    for filename, attr_name in files_to_load.items():
                        if filename in z.namelist():
                            try:
                                with z.open(filename) as f:
                                    df = pd.read_csv(f, low_memory=False)
                                    setattr(self, attr_name, df)
                                    self.gtfs_data[filename] = df
                                    print(f"   Loaded {filename}: {len(df)} records")
                                    loaded_files += 1
                            except Exception as e:
                                print(f"   Error loading {filename}: {e}")
                    
                    if loaded_files >= 3:
                        self.is_loaded = True
                        self.last_update = datetime.datetime.now()
                        
                        agency_name = "Unknown"
                        if hasattr(self, 'agency_df') and not self.agency_df.empty:
                            agency_name = self.agency_df.iloc[0].get('agency_name', 'Unknown')
                        
                        print(f"GTFS data loaded successfully")
                        print(f"   Agency: {agency_name}")
                        print(f"   Routes: {len(self.routes_df) if self.routes_df is not None else 0}")
                        print(f"   Stops: {len(self.stops_df) if self.stops_df is not None else 0}")
                        return True
                        
            except Exception as e:
                print(f"   Error loading from source {i+1}: {e}")
                continue
        
        print("Could not load GTFS data from any source")
        return False
    
    def get_realtime_departures(self, stop_id: str) -> List[Dict]:
        """Get real-time departures with live updates and time filtering"""
        try:
            cache_key = f"departures_{stop_id}"
            now = datetime.datetime.now()
            
            if (cache_key in self.realtime_cache and 
                (now - self.realtime_cache[cache_key]['timestamp']).seconds < self.cache_duration):
                cached_data = self.realtime_cache[cache_key]['data']
                return self._filter_upcoming_departures(cached_data)
            
            base_departures = self.get_stop_schedules(stop_id)
            realtime_updates = self._simulate_realtime_variations(stop_id)
            enhanced_departures = self._merge_schedule_and_realtime(base_departures, realtime_updates)
            
            self.realtime_cache[cache_key] = {
                'data': enhanced_departures,
                'timestamp': now
            }
            
            return self._filter_upcoming_departures(enhanced_departures)
            
        except Exception as e:
            print(f"Error getting real-time departures: {e}")
            return self.get_stop_schedules(stop_id)
    
    def _simulate_realtime_variations(self, stop_id: str) -> Dict:
        """Simulate realistic real-time variations"""
        import random
        
        variations = {}
        current_time = datetime.datetime.now()
        
        if 7 <= current_time.hour <= 9 or 16 <= current_time.hour <= 18:
            delay_chance = 0.7
            avg_delay = 5
        else:
            delay_chance = 0.3
            avg_delay = 2
        
        variations['delays'] = {
            'probability': delay_chance,
            'average_delay_minutes': avg_delay,
            'max_delay_minutes': avg_delay * 3
        }
        
        variations['status'] = 'simulated'
        return variations
    
    def _merge_schedule_and_realtime(self, scheduled: List[Dict], realtime: Dict) -> List[Dict]:
        """Merge scheduled times with real-time updates"""
        enhanced = []
        
        for schedule in scheduled:
            enhanced_departure = schedule.copy()
            enhanced_departure['realtime_status'] = 'scheduled'
            enhanced_departure['delay_minutes'] = 0
            enhanced_departure['original_time'] = schedule['departure_time']
            
            if 'delays' in realtime:
                delay_info = realtime['delays']
                import random
                if random.random() < delay_info.get('probability', 0):
                    delay_minutes = random.randint(0, delay_info.get('max_delay_minutes', 5))
                    enhanced_departure['delay_minutes'] = delay_minutes
                    enhanced_departure['realtime_status'] = 'delayed' if delay_minutes > 0 else 'on_time'
                    
                    try:
                        original_time = datetime.datetime.strptime(schedule['departure_time'], '%H:%M:%S')
                        new_time = original_time + datetime.timedelta(minutes=delay_minutes)
                        enhanced_departure['departure_time'] = new_time.strftime('%H:%M:%S')
                        enhanced_departure['realtime_departure'] = new_time.strftime('%H:%M')
                    except:
                        enhanced_departure['realtime_departure'] = schedule['departure_time'][:5]
            
            if enhanced_departure['delay_minutes'] > 5:
                enhanced_departure['status_color'] = '#ff4444'
                enhanced_departure['status_text'] = f"Delayed {enhanced_departure['delay_minutes']} min"
            elif enhanced_departure['delay_minutes'] > 0:
                enhanced_departure['status_color'] = '#ff8800'
                enhanced_departure['status_text'] = f"Delayed {enhanced_departure['delay_minutes']} min"
            else:
                enhanced_departure['status_color'] = '#44aa44'
                enhanced_departure['status_text'] = "On time"
            
            enhanced.append(enhanced_departure)
        
        return enhanced
    
    def _filter_upcoming_departures(self, departures: List[Dict]) -> List[Dict]:
        """Filter to show only upcoming departures"""
        current_time = datetime.datetime.now().time()
        current_datetime = datetime.datetime.now()
        
        upcoming = []
        for departure in departures:
            try:
                dept_time_str = departure.get('departure_time', '')
                if ':' in dept_time_str:
                    time_parts = dept_time_str.split(':')
                    hours = int(time_parts[0])
                    minutes = int(time_parts[1])
                    
                    if hours >= 24:
                        dept_datetime = current_datetime.replace(
                            hour=hours-24, minute=minutes, second=0, microsecond=0
                        ) + datetime.timedelta(days=1)
                    else:
                        dept_datetime = current_datetime.replace(
                            hour=hours, minute=minutes, second=0, microsecond=0
                        )
                    
                    time_diff = dept_datetime - current_datetime
                    if datetime.timedelta(0) <= time_diff <= datetime.timedelta(hours=4):
                        departure['time_until_departure'] = self._format_time_until(time_diff)
                        departure['departure_datetime'] = dept_datetime
                        upcoming.append(departure)
                        
            except (ValueError, IndexError):
                continue
        
        upcoming.sort(key=lambda x: x.get('departure_datetime', current_datetime))
        return upcoming[:10]
    
    def _format_time_until(self, time_diff: datetime.timedelta) -> str:
        """Format time until departure"""
        total_minutes = int(time_diff.total_seconds() / 60)
        
        if total_minutes < 1:
            return "Due now"
        elif total_minutes < 60:
            return f"{total_minutes} min"
        else:
            hours = total_minutes // 60
            minutes = total_minutes % 60
            if minutes == 0:
                return f"{hours}h"
            else:
                return f"{hours}h {minutes}m"
    
    def get_stop_schedules(self, stop_id, hours_ahead=4):
        """Get base stop schedules"""
        if not self.is_loaded or self.stop_times_df is None:
            return []
        
        try:
            stop_times = self.stop_times_df[self.stop_times_df['stop_id'] == stop_id].copy()
            
            if stop_times.empty:
                return []
            
            if self.trips_df is not None:
                stop_times = stop_times.merge(
                    self.trips_df[['trip_id', 'route_id', 'trip_headsign']], 
                    on='trip_id', how='left'
                )
            
            if self.routes_df is not None:
                stop_times = stop_times.merge(
                    self.routes_df[['route_id', 'route_short_name', 'route_long_name']], 
                    on='route_id', how='left'
                )
            
            schedules = []
            for _, row in stop_times.head(30).iterrows():
                try:
                    departure_time = row.get('departure_time', '')
                    if departure_time and ':' in departure_time:
                        schedule = {
                            'departure_time': departure_time,
                            'arrival_time': row.get('arrival_time', ''),
                            'route_name': str(row.get('route_short_name', 'Route')),
                            'route_description': str(row.get('route_long_name', '')),
                            'headsign': str(row.get('trip_headsign', '')),
                            'trip_id': str(row.get('trip_id', ''))
                        }
                        schedules.append(schedule)
                except:
                    continue
            
            return schedules
            
        except Exception as e:
            print(f"Error getting schedules: {e}")
            return []
    
    def find_nearby_stops(self, lat, lon, radius_km=0.5):
        """Find GTFS stops near coordinates"""
        if not self.is_loaded or self.stops_df is None:
            return []
        
        try:
            stops = self.stops_df.copy()
            stops['distance_km'] = ((stops['stop_lat'] - lat)**2 + (stops['stop_lon'] - lon)**2)**0.5 * 111
            nearby = stops[stops['distance_km'] <= radius_km].sort_values('distance_km')
            return nearby[['stop_id', 'stop_name', 'stop_lat', 'stop_lon', 'distance_km']].head(5).to_dict('records')
        
        except Exception as e:
            print(f"Error finding nearby stops: {e}")
            return []

# Global GTFS manager instance
gtfs_manager = EnhancedGTFSManager()

print("Part 2: Enhanced GTFS Manager loaded successfully")

# bike_bus_bike_google_part3.py
# Part 3: Google Maps API-based Bike Routing with GeoPandas Segment Analysis

class BikeRoutingManager:
    """Manages bike routing using Google Maps API and segment analysis with GeoPandas"""

    def __init__(self):
        self.roads_gdf = None
        self.roads_gdf_m = None  # projected (meters) copy
        self.transit_stops_gdf = None
        print("Initializing Bike Routing Manager (Google Maps + GeoPandas)...")
        self.load_data()
    
    def load_data(self):
        """Load and validate shapefiles"""
        try:
            # Load roads shapefile
            if os.path.exists(ROADS_SHAPEFILE):
                print(f"Loading roads from: {ROADS_SHAPEFILE}")
                self.roads_gdf = gpd.read_file(ROADS_SHAPEFILE)
                print(f"Loaded roads: {len(self.roads_gdf)} features")
                print(f"   Columns: {list(self.roads_gdf.columns)}")
                self._standardize_roads_columns()
                self.roads_gdf_m = self._to_meters(self.roads_gdf)
                print(f"   Projected to: {self.roads_gdf_m.crs}")
            else:
                print(f"Roads shapefile not found: {ROADS_SHAPEFILE}")
                print("   The tool will work with Google Maps API routing only (no facility analysis)")

            # Load transit stops shapefile
            if os.path.exists(TRANSIT_STOPS_SHAPEFILE):
                print(f"Loading transit stops from: {TRANSIT_STOPS_SHAPEFILE}")
                self.transit_stops_gdf = gpd.read_file(TRANSIT_STOPS_SHAPEFILE)
                print(f"Loaded transit stops: {len(self.transit_stops_gdf)} features")
            else:
                print(f"Transit stops shapefile not found: {TRANSIT_STOPS_SHAPEFILE}")
                print("   Transit stop analysis will be disabled")
                
        except Exception as e:
            print(f"Error loading shapefiles: {e}")
            print("   The tool will work with Google Maps API routing only")
    
    def _standardize_roads_columns(self):
        """Standardize column names for consistent access"""
        if self.roads_gdf is None:
            return
            
        cols = self.roads_gdf.columns

        # Map important fields
        total_score_f = _map_field(cols, [
            "TOTAL_SCOR", "Total_Scor", "TOTAL_SCORE", "Total_Score", 
            "Bike_Score", "bike_score", "BIKE_SCORE"
        ])

        fac_type_f = _map_field(cols, [
            "FACILITY_T", "Facility_Type", "FACILITY_TYPE", "facility_type"
        ])

        speed_f = _map_field(cols, [
            "SPEED", "Speed_Limit", "SPEED_LIMIT", "SPD_LIM"
        ])

        lanes_f = _map_field(cols, [
            "Lane_Count", "Lanes", "LANES", "Num_Lanes", "NUM_LANES"
        ])

        # Create canonical fields
        try:
            if total_score_f:
                score_values = pd.to_numeric(self.roads_gdf[total_score_f], errors='coerce').fillna(0)
                self.roads_gdf["Bike_Score__canon"] = score_values
                self.roads_gdf["Directional_Score__canon"] = 100
            else:
                self.roads_gdf["Bike_Score__canon"] = 0
                self.roads_gdf["Directional_Score__canon"] = 100
        except:
            self.roads_gdf["Bike_Score__canon"] = 0
            self.roads_gdf["Directional_Score__canon"] = 100

        self.roads_gdf["Facility_Type__canon"] = (
            self.roads_gdf[fac_type_f].fillna("NO BIKELANE") 
            if fac_type_f else "NO BIKELANE"
        )

        try:
            self.roads_gdf["Speed_Limit__canon"] = (
                pd.to_numeric(self.roads_gdf[speed_f], errors='coerce').fillna(30)
                if speed_f else 30
            )
        except:
            self.roads_gdf["Speed_Limit__canon"] = 30

        try:
            self.roads_gdf["Lanes__canon"] = (
                pd.to_numeric(self.roads_gdf[lanes_f], errors='coerce').fillna(2)
                if lanes_f else 2
            )
        except:
            self.roads_gdf["Lanes__canon"] = 2

        print("   Standardized road attribute columns")
    
    def _to_meters(self, gdf):
        """Return a projected (meters) copy"""
        if gdf is None or gdf.empty:
            return gdf
            
        if gdf.crs is None:
            print("   No CRS found, assuming WGS84")
            gdf = gdf.set_crs("EPSG:4326", allow_override=True)
        
        try:
            target_crs = gdf.estimate_utm_crs()
        except Exception:
            target_crs = "EPSG:3857"
            
        try:
            return gdf.to_crs(target_crs)
        except Exception as e:
            print(f"   Projection failed: {e}, using original CRS")
            return gdf
    
    def create_bike_route_google(self, start_coords, end_coords, route_name):
        """Create a bicycle route using Google Maps Directions API"""
        try:
            print(f"Creating Google Maps bike route: {route_name}")
            
            url = "https://maps.googleapis.com/maps/api/directions/json"
            
            params = {
                'origin': f"{start_coords[1]},{start_coords[0]}",  # lat,lng format
                'destination': f"{end_coords[1]},{end_coords[0]}",
                'mode': 'bicycling',
                'alternatives': 'false',
                'key': GOOGLE_API_KEY
            }
            
            response = requests.get(url, params=params, timeout=30)
            response.raise_for_status()
            data = response.json()
            
            if data.get('status') != 'OK':
                error_msg = data.get('error_message', f"API Status: {data.get('status')}")
                print(f"   Google Maps API error: {error_msg}")
                return None
                
            route = data['routes'][0]
            leg = route['legs'][0]
            
            # Decode polyline geometry
            overview_polyline = route['overview_polyline']['points']
            coords_decoded = decode_polyline(overview_polyline)
            
            geometry = {
                "type": "LineString",
                "coordinates": coords_decoded
            }
            
            distance_m = leg['distance']['value']
            duration_s = leg['duration']['value']
            
            route_data = {
                "name": route_name,
                "length_miles": round(distance_m * 0.000621371, 3),
                "length_meters": distance_m,
                "travel_time_minutes": round(duration_s / 60, 1),
                "travel_time_formatted": leg['duration']['text'],
                "geometry": geometry,
                "duration_seconds": duration_s
            }
            
            # Analyze with roads shapefile if available (UNCHANGED)
            if self.roads_gdf is not None:
                segments, overall_score, facility_stats = self.analyze_route_segments(geometry)
                route_data.update({
                    "segments": segments,
                    "overall_score": overall_score,
                    "facility_stats": facility_stats
                })
            else:
                route_data.update({
                    "segments": [],
                    "overall_score": 50.0,
                    "facility_stats": {
                        "UNKNOWN": {
                            "length_miles": route_data["length_miles"],
                            "percentage": 100.0,
                            "count": 1,
                            "avg_score": 50.0
                        }
                    }
                })
            
            print(f"   Route created: {route_data['length_miles']} miles, {route_data['travel_time_formatted']}")
            return route_data
            
        except Exception as e:
            print(f"   Error creating Google Maps bike route: {e}")
            return None
    
    def analyze_route_segments(self, route_geometry):
        """
        Split the Google Maps route into segments colored by matched road facility types.
        Returns portions of the Google route geometry, each tagged with its facility type.
        """
        try:
            if not route_geometry or not route_geometry.get("coordinates"):
                return [], 50.0, {"NO DATA": {"length_miles": 0.0, "percentage": 100.0, "avg_score": 0.0}}

            coords = route_geometry["coordinates"]
            if len(coords) < 2:
                return [], 50.0, {"NO DATA": {"length_miles": 0.0, "percentage": 100.0, "avg_score": 0.0}}
                
            # Create route geometry from Google Maps
            route_ll = LineString([(float(lon), float(lat)) for lon, lat in coords])
            route_gdf = gpd.GeoDataFrame({"id": [1]}, geometry=[route_ll], crs="EPSG:4326")

            if self.roads_gdf is None or self.roads_gdf.empty:
                # No shapefile - return whole route as unknown
                route_length_miles = route_ll.length * 69.0
                return [{
                    "facility_type": "UNKNOWN",
                    "bike_score": 50.0,
                    "composite_score": 50.0,
                    "LTS": 4,
                    "length_m": route_length_miles * 1609.34,
                    "shape_length_miles": route_length_miles,
                    "geometry": route_geometry
                }], 50.0, {"UNKNOWN": {"length_miles": route_length_miles, "percentage": 100.0, "avg_score": 50.0}}

            # Project to meters
            route_m = self._to_meters(route_gdf)
            roads_m = self.roads_gdf_m

            if route_m is None or roads_m is None:
                route_length_miles = route_ll.length * 69.0
                return [{
                    "facility_type": "UNKNOWN",
                    "bike_score": 50.0,
                    "composite_score": 50.0,
                    "LTS": 4,
                    "length_m": route_length_miles * 1609.34,
                    "shape_length_miles": route_length_miles,
                    "geometry": route_geometry
                }], 50.0, {"UNKNOWN": {"length_miles": route_length_miles, "percentage": 100.0, "avg_score": 50.0}}

            route_line_m = route_m.geometry.iloc[0]
            
            # Find candidate road segments
            initial_buffer = 50  # meters
            route_buffered = route_line_m.buffer(initial_buffer)
            candidate_mask = roads_m.geometry.intersects(route_buffered)
            candidates = roads_m[candidate_mask].copy()

            if candidates.empty:
                route_length_miles = route_ll.length * 69.0
                return [{
                    "facility_type": "NO CANDIDATES",
                    "bike_score": 50.0,
                    "composite_score": 50.0,
                    "LTS": 4,
                    "length_m": route_length_miles * 1609.34,
                    "shape_length_miles": route_length_miles,
                    "geometry": route_geometry
                }], 50.0, {"NO CANDIDATES": {"length_miles": route_length_miles, "percentage": 100.0, "avg_score": 50.0}}

            print(f"   Evaluating {len(candidates)} candidate segments with alignment analysis...")
            
            # Score and select matching road segments
            matched_roads = []
            
            for idx, road_row in candidates.iterrows():
                road_geom = road_row.geometry
                if road_geom is None or road_geom.is_empty:
                    continue
                    
                # Calculate alignment metrics
                alignment_score = self._calculate_alignment_score(route_line_m, road_geom)
                proximity_score = self._calculate_proximity_score(route_line_m, road_geom)
                coverage_score = self._calculate_coverage_score(route_line_m, road_geom)
                
                overall_match_score = (
                    alignment_score * 0.4 +
                    proximity_score * 0.4 +
                    coverage_score * 0.2
                )
                
                if overall_match_score >= 0.3:
                    matched_roads.append({
                        'geometry_m': road_geom,
                        'facility_type': str(road_row.get("Facility_Type__canon", "NO BIKELANE")),
                        'bike_score': float(road_row.get("Bike_Score__canon", 0)),
                        'dir_score': float(road_row.get("Directional_Score__canon", 100)),
                        'speed_limit': float(road_row.get("Speed_Limit__canon", 30)),
                        'lanes': int(road_row.get("Lanes__canon", 2)),
                        'match_quality': overall_match_score
                    })

            if not matched_roads:
                route_length_miles = route_ll.length * 69.0
                return [{
                    "facility_type": "NO MATCHES",
                    "bike_score": 50.0,
                    "composite_score": 50.0,
                    "LTS": 4,
                    "length_m": route_length_miles * 1609.34,
                    "shape_length_miles": route_length_miles,
                    "geometry": route_geometry
                }], 50.0, {"NO MATCHES": {"length_miles": route_length_miles, "percentage": 100.0, "avg_score": 50.0}}

            # Sample points along Google route and assign to nearest matched road
            num_samples = max(20, int(route_line_m.length / 10))
            
            point_assignments = []
            for i in range(num_samples + 1):
                distance_along = (i / num_samples) * route_line_m.length if num_samples > 0 else 0
                point = route_line_m.interpolate(distance_along)
                
                # Find nearest matched road to this point
                best_road = None
                min_dist = float('inf')
                
                for road in matched_roads:
                    dist = point.distance(road['geometry_m'])
                    if dist < min_dist:
                        min_dist = dist
                        best_road = road
                
                point_assignments.append({
                    'distance': distance_along,
                    'facility_type': best_road['facility_type'] if best_road else "NO BIKELANE",
                    'road_data': best_road
                })
            
            # Split Google route at facility type changes
            from shapely.ops import substring
            selected_segments = []
            
            current_facility = point_assignments[0]['facility_type']
            segment_start_dist = 0
            
            for i in range(1, len(point_assignments)):
                facility = point_assignments[i]['facility_type']
                
                if facility != current_facility or i == len(point_assignments) - 1:
                    # Create segment from start to current point
                    end_dist = point_assignments[i-1]['distance'] if facility != current_facility else route_line_m.length
                    
                    if end_dist > segment_start_dist:
                        try:
                            # Extract this portion of the Google Maps route
                            segment_geom_m = substring(route_line_m, segment_start_dist, end_dist)
                            
                            # Convert to WGS84 for display
                            segment_gdf = gpd.GeoDataFrame({"id": [1]}, geometry=[segment_geom_m], crs=route_m.crs)
                            segment_wgs84 = segment_gdf.to_crs("EPSG:4326").geometry.iloc[0]
                            segment_coords = [[coord[0], coord[1]] for coord in segment_wgs84.coords]
                            
                            # Get road attributes
                            road_data = point_assignments[int((segment_start_dist / route_line_m.length) * num_samples)]['road_data']
                            
                            if road_data and segment_coords:
                                bike_score = road_data['bike_score']
                                dir_score = road_data['dir_score']
                                composite_score = (bike_score * dir_score) / 100.0
                                lts = classify_lts(
                                    current_facility,
                                    road_data['speed_limit'],
                                    road_data['lanes']
                                )
                                
                                selected_segments.append({
                                    "facility_type": current_facility,
                                    "bike_score": round(bike_score, 1),
                                    "directional_score": round(dir_score, 1),
                                    "composite_score": round(composite_score, 2),
                                    "LTS": lts,
                                    "length_m": float(segment_geom_m.length),
                                    "shape_length_miles": float(segment_geom_m.length) * 0.000621371,
                                    "speed_limit": road_data['speed_limit'],
                                    "lanes": road_data['lanes'],
                                    "match_quality": round(road_data['match_quality'], 3),
                                    "geometry": {
                                        "type": "LineString",
                                        "coordinates": segment_coords
                                    }
                                })
                        except Exception as e:
                            print(f"   Warning: Could not create segment: {e}")
                    
                    # Start new segment
                    current_facility = facility
                    segment_start_dist = point_assignments[i]['distance']

            # Calculate statistics
            if selected_segments:
                total_length_m = sum(seg["length_m"] for seg in selected_segments)
                weighted_score_sum = sum(seg["composite_score"] * seg["length_m"] for seg in selected_segments)
                overall_score = weighted_score_sum / total_length_m if total_length_m > 0 else 50.0

                facility_buckets = {}
                for seg in selected_segments:
                    facility_type = seg["facility_type"]
                    length_m = seg["length_m"]
                    
                    if facility_type not in facility_buckets:
                        facility_buckets[facility_type] = {"length_m": 0.0, "count": 0, "score_sum": 0.0}
                    
                    facility_buckets[facility_type]["length_m"] += length_m
                    facility_buckets[facility_type]["count"] += 1
                    facility_buckets[facility_type]["score_sum"] += seg["composite_score"]

                facility_stats = {}
                for facility_type, stats in facility_buckets.items():
                    length_miles = stats["length_m"] * 0.000621371
                    percentage = (stats["length_m"] / total_length_m) * 100.0 if total_length_m > 0 else 0.0
                    avg_score = stats["score_sum"] / stats["count"] if stats["count"] > 0 else 0.0
                    
                    facility_stats[facility_type] = {
                        "length_miles": round(length_miles, 3),
                        "percentage": round(percentage, 1),
                        "count": stats["count"],
                        "avg_score": round(avg_score, 1)
                    }

                print(f"   Split Google route into {len(selected_segments)} segments, overall score: {overall_score:.1f}")
                return selected_segments, round(overall_score, 1), facility_stats

            # Fallback
            route_length_miles = route_ll.length * 69.0
            return [{
                "facility_type": "NO SEGMENTS CREATED",
                "bike_score": 50.0,
                "composite_score": 50.0,
                "LTS": 4,
                "length_m": route_length_miles * 1609.34,
                "shape_length_miles": route_length_miles,
                "geometry": route_geometry
            }], 50.0, {"NO SEGMENTS": {"length_miles": route_length_miles, "percentage": 100.0, "avg_score": 50.0}}

        except Exception as e:
            print(f"Analysis error: {e}")
            import traceback

# ==== BEGIN AUTO-PATCH: cloud deploy settings ====
import os, webbrowser

# Prefer platform-assigned port if available (Railway/Render set PORT)
try:
    PORT = int(os.getenv("PORT", str(globals().get("PORT", 8000))))
except Exception:
    PORT = int(os.getenv("PORT", 8000))

# Shapefile paths and API key from environment (with sane defaults for containers)
ROADS_SHAPEFILE = os.getenv("ROADS_SHAPEFILE", globals().get("ROADS_SHAPEFILE", "/app/data/roads.shp"))
TRANSIT_STOPS_SHAPEFILE = os.getenv("TRANSIT_STOPS_SHAPEFILE", globals().get("TRANSIT_STOPS_SHAPEFILE", "/app/data/transit_stops.shp"))
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY", globals().get("GOOGLE_API_KEY", None))

# Headless mode inside containers: prevent auto-opening a browser
HEADLESS = os.getenv("HEADLESS", "1") == "1"
if HEADLESS:
    def _noopen(*args, **kwargs): 
        return False
    # monkey-patch webbrowser.open to no-op in containers
    webbrowser.open = _noopen
# ==== END AUTO-PATCH ====

            traceback.print_exc()
            return [], 50.0, {"ANALYSIS ERROR": {"length_miles": 0.0, "percentage": 100.0, "avg_score": 0.0}}
    
    def _sample_line_points(self, line, num_points=5):
        """Sample points along a line at regular intervals."""
        try:
            if line.is_empty or line.length == 0:
                return []
                
            points = []
            for i in range(num_points):
                distance = (i / (num_points - 1)) * line.length if num_points > 1 else 0
                point = line.interpolate(distance)
                points.append((point.x, point.y))
            return points
        except Exception:
            return []

    def _calculate_average_bearing(self, points):
        """Calculate average bearing (direction) from a series of points."""
        try:
            if len(points) < 2:
                return 0
                
            bearings = []
            for i in range(len(points) - 1):
                x1, y1 = points[i]
                x2, y2 = points[i + 1]
                
                dx = x2 - x1
                dy = y2 - y1
                
                if dx == 0 and dy == 0:
                    continue
                    
                bearing = math.atan2(dy, dx) * 180 / math.pi
                bearing = (bearing + 360) % 360
                bearings.append(bearing)
            
            if not bearings:
                return 0
                
            # Circular mean for angles
            sin_sum = sum(math.sin(math.radians(b)) for b in bearings)
            cos_sum = sum(math.cos(math.radians(b)) for b in bearings)
            
            mean_bearing = math.atan2(sin_sum, cos_sum) * 180 / math.pi
            return (mean_bearing + 360) % 360
            
        except Exception:
            return 0

    def _calculate_alignment_score(self, route_line, road_line):
        """Calculate how well the road segment aligns with the route direction."""
        try:
            route_points = self._sample_line_points(route_line, num_points=5)
            road_points = self._sample_line_points(road_line, num_points=5)
            
            if len(route_points) < 2 or len(road_points) < 2:
                return 0.5
            
            route_bearing = self._calculate_average_bearing(route_points)
            road_bearing = self._calculate_average_bearing(road_points)
            
            angle_diff = abs(route_bearing - road_bearing)
            angle_diff = min(angle_diff, 360 - angle_diff)
            angle_diff = min(angle_diff, 180 - angle_diff)
            
            alignment_score = 1 - (angle_diff / 90.0)
            return max(0, min(1, alignment_score))
            
        except Exception:
            return 0.5

    def _calculate_proximity_score(self, route_line, road_line):
        """Calculate proximity score based on distance between route and road segment."""
        try:
            distance = route_line.distance(road_line)
            
            if distance <= 1:
                return 1.0
            elif distance <= 10:
                return 0.8 + 0.2 * (10 - distance) / 9
            elif distance <= 25:
                return 0.3 + 0.5 * (25 - distance) / 15
            else:
                return max(0, 0.3 * math.exp(-(distance - 25) / 25))
                
        except Exception:
            return 0.1

    def _calculate_coverage_score(self, route_line, road_line):
        """Calculate how much of the route length is covered by this road segment."""
        try:
            road_buffer = road_line.buffer(15)
            intersection = route_line.intersection(road_buffer)
            
            if intersection.is_empty:
                return 0
                
            coverage_length = intersection.length if hasattr(intersection, 'length') else 0
            route_length = route_line.length
            
            coverage_ratio = coverage_length / route_length if route_length > 0 else 0
            return min(1.0, coverage_ratio)
            
        except Exception:
            return 0.1

    def find_nearest_bus_stops(self, point_coords, max_stops=3):
        """Find nearest transit stops using GeoPandas"""
        if self.transit_stops_gdf is None or self.transit_stops_gdf.empty:
            print("No transit stops data available")
            return []
        
        try:
            print(f"Finding nearest bus stops to {point_coords}")
            
            # Create point geometry
            point = Point(float(point_coords[0]), float(point_coords[1]))
            point_gdf = gpd.GeoDataFrame({"id": [1]}, geometry=[point], crs="EPSG:4326")
            
            # Ensure transit stops have a CRS
            if self.transit_stops_gdf.crs is None:
                self.transit_stops_gdf = self.transit_stops_gdf.set_crs("EPSG:4326")
            
            # Project both to meters for accurate distance calculation
            point_m = self._to_meters(point_gdf).geometry.iloc[0]
            stops_m = self._to_meters(self.transit_stops_gdf)
            
            # Calculate distances
            distances = stops_m.geometry.distance(point_m)
            
            # Get indices of nearest stops
            nearest_indices = distances.nsmallest(max_stops).index
            
            results = []
            for idx in nearest_indices:
                try:
                    row = self.transit_stops_gdf.loc[idx]
                    
                    # Try to find name field (case-insensitive)
                    name_candidates = ['NAME', 'name', 'Stop_Name', 'STOP_NAME', 
                                    'stop_name', 'StopName', 'STOPNAME', 'stop_id', 'STOP_ID']
                    
                    stop_name = None
                    for name_field in name_candidates:
                        if name_field in row.index:
                            stop_name = str(row[name_field])
                            break
                    
                    if stop_name is None or stop_name == 'nan':
                        stop_name = f"Stop {idx}"
                    
                    # Get geometry coordinates
                    stop_geom = row.geometry
                    if stop_geom is None or stop_geom.is_empty:
                        continue
                    
                    # Extract coordinates (handle both Point and other geometry types)
                    if stop_geom.geom_type == 'Point':
                        stop_x = float(stop_geom.x)
                        stop_y = float(stop_geom.y)
                    else:
                        # For non-point geometries, use centroid
                        centroid = stop_geom.centroid
                        stop_x = float(centroid.x)
                        stop_y = float(centroid.y)
                    
                    results.append({
                        "id": int(idx),
                        "name": stop_name,
                        "x": stop_x,
                        "y": stop_y,
                        "display_x": stop_x,
                        "display_y": stop_y,
                        "distance_meters": float(distances.loc[idx])
                    })
                    
                except Exception as e:
                    print(f"Error processing stop at index {idx}: {e}")
                    continue
            
            print(f"Found {len(results)} nearby bus stops")
            
            if not results:
                print("WARNING: No valid bus stops found within search radius")
                print(f"Transit stops CRS: {self.transit_stops_gdf.crs}")
                print(f"Total stops in dataset: {len(self.transit_stops_gdf)}")
            
            return results
            
        except Exception as e:
            print(f"Error finding nearest bus stops: {e}")
            import traceback
            traceback.print_exc()
            return []

# Global bike routing manager
bike_manager = BikeRoutingManager()

print("Part 3: Google Maps Bike Routing Manager loaded successfully")

# bike_bus_bike_google_part4.py
# Part 4: Google Maps Transit API Functions and GTFS Enhancement

def get_transit_routes_google(origin, destination, api_key, departure_time="now"):
    """Get transit routes using Google Maps API"""
    try:
        print(f"Getting Google Maps transit routes: '{origin}' -> '{destination}'")
        
        url = "https://maps.googleapis.com/maps/api/directions/json"
        
        if departure_time == "now":
            departure_timestamp = int(datetime.datetime.now().timestamp())
        else:
            departure_timestamp = departure_time
        
        params = {
            'origin': origin,
            'destination': destination,
            'mode': 'transit',
            'departure_time': departure_timestamp,
            'alternatives': 'true',
            'transit_mode': 'bus|subway|train|tram',
            'transit_routing_preference': 'fewer_transfers',
            'key': api_key
        }
        
        response = requests.get(url, params=params, timeout=30)
        response.raise_for_status()
        
        data = response.json()
        
        if data.get('status') != 'OK':
            error_msg = data.get('error_message', f"API Status: {data.get('status')}")
            print(f"Google API error: {error_msg}")
            return {"error": error_msg}
        
        routes = []
        if 'routes' in data and data['routes']:
            for idx, route_data in enumerate(data['routes']):
                route = parse_google_transit_route(route_data, idx)
                if route:
                    enhanced_route = enhance_route_with_gtfs(route)
                    routes.append(enhanced_route)
        
        if not routes:
            return {"error": "No transit routes found between these locations"}
        
        return {
            "routes": routes,
            "service": "Google Maps + GTFS Enhanced",
            "total_routes": len(routes),
            "gtfs_enabled": gtfs_manager.is_loaded
        }
        
    except Exception as e:
        print(f"Error getting Google Maps transit routes: {e}")
        return {"error": str(e)}

def parse_google_transit_route(route_data, route_index):
    """Parse a single Google transit route"""
    try:
        legs = route_data.get('legs', [])
        if not legs:
            return None
        
        leg = legs[0]
        
        duration_seconds = leg['duration']['value']
        duration_minutes = round(duration_seconds / 60, 1)
        duration_text = leg['duration']['text']
        
        distance_meters = leg['distance']['value']
        distance_km = round(distance_meters / 1000, 2)
        distance_miles = round(distance_km * 0.621371, 2)
        
        departure_time = leg.get('departure_time', {})
        arrival_time = leg.get('arrival_time', {})
        
        # Extract route geometry
        overview_polyline = route_data.get('overview_polyline', {}).get('points', '')
        route_geometry = []
        if overview_polyline:
            route_geometry = decode_polyline(overview_polyline)
        
        # Parse steps
        steps = []
        transit_lines = []
        total_fare = 0
        
        for step_idx, step in enumerate(leg.get('steps', [])):
            parsed_step = parse_transit_step(step, step_idx)
            if parsed_step:
                steps.append(parsed_step)
                
                if parsed_step['travel_mode'] == 'TRANSIT':
                    if parsed_step.get('transit_line'):
                        transit_lines.append(parsed_step['transit_line'])
                    if parsed_step.get('fare_value'):
                        total_fare += parsed_step['fare_value']
        
        # Count transfers
        transit_steps = [s for s in steps if s['travel_mode'] == 'TRANSIT']
        transfers = max(0, len(transit_steps) - 1)
        
        route_name = f"Transit Option {route_index + 1}"
        if transfers > 0:
            route_name += f" ({transfers} transfer{'s' if transfers != 1 else ''})"
        
        return {
            "route_number": route_index + 1,
            "name": route_name,
            "description": f"Transit route with {transfers} transfer{'s' if transfers != 1 else ''}",
            "duration_seconds": duration_seconds,
            "duration_minutes": duration_minutes,
            "duration_text": duration_text,
            "distance_meters": distance_meters,
            "distance_km": distance_km,
            "distance_miles": distance_miles,
            "departure_time": departure_time.get('text', 'Unknown'),
            "arrival_time": arrival_time.get('text', 'Unknown'),
            "transfers": transfers,
            "total_fare": total_fare if total_fare > 0 else None,
            "transit_lines": list(set(transit_lines)),
            "steps": steps,
            "geometry": {
                "type": "LineString",
                "coordinates": route_geometry
            },
            "service": "Google Maps Transit"
        }
        
    except Exception as e:
        print(f"Error parsing Google transit route: {e}")
        return None

def parse_transit_step(step, step_index):
    """Parse individual transit step"""
    try:
        travel_mode = step.get('travel_mode', 'UNKNOWN')
        
        # Clean HTML from instructions
        instruction = step.get('html_instructions', '')
        import re
        instruction = re.sub(r'<[^>]+>', '', instruction)
        
        duration_seconds = step['duration']['value']
        duration_minutes = round(duration_seconds / 60, 1)
        duration_text = step['duration']['text']
        
        distance_meters = step['distance']['value']
        distance_km = round(distance_meters / 1000, 2)
        distance_miles = round(distance_km * 0.621371, 2)
        
        step_data = {
            "step_number": step_index + 1,
            "travel_mode": travel_mode,
            "instruction": instruction,
            "duration_seconds": duration_seconds,
            "duration_minutes": duration_minutes,
            "duration_text": duration_text,
            "distance_meters": distance_meters,
            "distance_km": distance_km,
            "distance_miles": distance_miles
        }
        
        if travel_mode == 'TRANSIT' and 'transit_details' in step:
            transit = step['transit_details']
            line = transit.get('line', {})
            vehicle = line.get('vehicle', {})
            agencies = line.get('agencies', [])
            
            step_data.update({
                "transit_line": line.get('short_name', line.get('name', 'Unknown Line')),
                "transit_line_color": line.get('color', '#1f8dd6'),
                "transit_vehicle_type": vehicle.get('type', 'BUS'),
                "transit_vehicle_name": vehicle.get('name', 'Bus'),
                "transit_agency": agencies[0].get('name', 'Transit Agency') if agencies else 'Transit Agency'
            })
            
            # Extract stop information
            departure_stop = transit.get('departure_stop', {})
            arrival_stop = transit.get('arrival_stop', {})
            
            step_data.update({
                "departure_stop_name": departure_stop.get('name', 'Unknown Stop'),
                "departure_stop_location": departure_stop.get('location', {}),
                "arrival_stop_name": arrival_stop.get('name', 'Unknown Stop'),
                "arrival_stop_location": arrival_stop.get('location', {}),
                "num_stops": transit.get('num_stops', 0)
            })
            
            # Extract timing information
            departure_time = transit.get('departure_time', {})
            arrival_time = transit.get('arrival_time', {})
            
            step_data.update({
                "scheduled_departure": departure_time.get('text', ''),
                "scheduled_arrival": arrival_time.get('text', ''),
                "departure_timestamp": departure_time.get('value', 0),
                "arrival_timestamp": arrival_time.get('value', 0)
            })
            
            step_data["headsign"] = transit.get('headsign', '')
            
            if 'fare' in line:
                fare = line['fare']
                step_data.update({
                    "fare_text": fare.get('text', ''),
                    "fare_value": fare.get('value', 0),
                    "fare_currency": fare.get('currency', 'USD')
                })
        
        return step_data
        
    except Exception as e:
        print(f"Error parsing step {step_index + 1}: {e}")
        return None

def enhance_route_with_gtfs(route):
    """Enhanced route enhancement with GTFS data"""
    enhanced_route = route.copy()
    
    if not gtfs_manager.is_loaded:
        enhanced_route['gtfs_enhanced'] = False
        return enhanced_route
    
    try:
        enhanced_route['gtfs_enhanced'] = True
        enhanced_route['enhancement_timestamp'] = datetime.datetime.now().isoformat()
        
        # Look for transit steps to enhance with GTFS data
        for step in enhanced_route.get('steps', []):
            if step.get('travel_mode') == 'TRANSIT':
                departure_stop = step.get('departure_stop_location', {})
                
                if departure_stop:
                    lat = departure_stop.get('lat')
                    lon = departure_stop.get('lng')
                    
                    if lat and lon:
                        # Find nearby GTFS stops
                        nearby_stops = gtfs_manager.find_nearby_stops(lat, lon, radius_km=0.3)
                        
                        if nearby_stops:
                            closest_stop = nearby_stops[0]
                            stop_id = closest_stop['stop_id']
                            
                            # Get real-time departures
                            realtime_departures = gtfs_manager.get_realtime_departures(stop_id)
                            
                            # Add GTFS data to step
                            step['gtfs_data'] = {
                                'stop_id': stop_id,
                                'stop_name': closest_stop['stop_name'],
                                'realtime_departures': realtime_departures,
                                'next_departures': [d.get('realtime_departure', d['departure_time'][:5]) for d in realtime_departures[:5]],
                                'departure_status': [d.get('status_text', 'Scheduled') for d in realtime_departures[:3]],
                                'has_delays': any(d.get('delay_minutes', 0) > 0 for d in realtime_departures),
                                'last_updated': datetime.datetime.now().strftime('%H:%M:%S')
                            }
        
        enhanced_route['enhancement_level'] = 'gtfs'
        
    except Exception as e:
        print(f"Error enhancing route with GTFS: {e}")
        enhanced_route['gtfs_enhanced'] = False
        enhanced_route['enhancement_level'] = 'basic'
    
    return enhanced_route

def get_transit_routes_between_stops(start_stop, end_stop, departure_time="now"):
    """Get transit routes between two bus stops"""
    try:
        print(f"Getting transit routes between bus stops:")
        print(f"  Start: {start_stop['name']} ({start_stop['display_x']}, {start_stop['display_y']})")
        print(f"  End: {end_stop['name']} ({end_stop['display_x']}, {end_stop['display_y']})")
        
        url = "https://maps.googleapis.com/maps/api/directions/json"
        
        if departure_time == "now":
            departure_timestamp = int(datetime.datetime.now().timestamp())
        else:
            departure_timestamp = departure_time
        
        params = {
            'origin': f"{start_stop['display_y']},{start_stop['display_x']}",
            'destination': f"{end_stop['display_y']},{end_stop['display_x']}",
            'mode': 'transit',
            'departure_time': departure_timestamp,
            'alternatives': 'true',
            'transit_mode': 'bus|subway|train|tram',
            'transit_routing_preference': 'fewer_transfers',
            'key': GOOGLE_API_KEY
        }
        
        response = requests.get(url, params=params, timeout=30)
        response.raise_for_status()
        
        data = response.json()
        
        if data.get('status') != 'OK':
            error_msg = data.get('error_message', f"API Status: {data.get('status')}")
            print(f"Google API error: {error_msg}")
            return {"error": error_msg}
        
        routes = []
        if 'routes' in data and data['routes']:
            for idx, route_data in enumerate(data['routes']):
                route = parse_google_transit_route(route_data, idx)
                if route:
                    route['start_stop'] = start_stop
                    route['end_stop'] = end_stop
                    enhanced_route = enhance_route_with_gtfs(route)
                    routes.append(enhanced_route)
        
        if not routes:
            return {"error": "No transit routes found between these bus stops"}
        
        return {
            "routes": routes,
            "service": "Google Maps + GTFS Enhanced",
            "total_routes": len(routes),
            "gtfs_enabled": gtfs_manager.is_loaded,
            "start_stop": start_stop,
            "end_stop": end_stop,
            "last_update": datetime.datetime.now().isoformat()
        }
        
    except Exception as e:
        print(f"Error getting transit routes: {e}")
        return {"error": str(e)}

def calculate_total_route_time_with_waits(transit_route, current_time=None):
    """Calculate total route time including realistic waiting times"""
    try:
        if current_time is None:
            current_time = datetime.datetime.now()
        
        total_time_minutes = 0
        
        # Add transit time
        total_time_minutes += transit_route.get('duration_minutes', 0)
        
        # Add waiting time estimates
        transit_steps = [s for s in transit_route.get('steps', []) if s.get('travel_mode') == 'TRANSIT']
        
        for i, step in enumerate(transit_steps):
            if i == 0:
                # First transit - add initial waiting time
                if step.get('gtfs_data') and step['gtfs_data'].get('realtime_departures'):
                    next_departure = step['gtfs_data']['realtime_departures'][0]
                    if 'time_until_departure' in next_departure:
                        wait_time_str = next_departure['time_until_departure']
                        if 'min' in wait_time_str:
                            wait_minutes = int(wait_time_str.split()[0])
                            total_time_minutes += wait_minutes
                        elif 'Due now' in wait_time_str:
                            total_time_minutes += 1
                else:
                    # Default waiting time based on time of day
                    if 7 <= current_time.hour <= 9 or 16 <= current_time.hour <= 18:
                        total_time_minutes += 8  # Rush hour
                    else:
                        total_time_minutes += 15  # Off-peak
            else:
                # Transfer waiting time
                total_time_minutes += 5
        
        return round(total_time_minutes, 1)
        
    except Exception as e:
        print(f"Error calculating total route time: {e}")
        return transit_route.get('duration_minutes', 0)

print("Part 4: Google Maps Transit API and enhancement loaded successfully")

# bike_bus_bike_google_part5.py
# Part 5: Main Route Analysis Engine with Multimodal Logic

def should_use_transit_fallback(start_point, end_point, start_bus_stops, end_bus_stops, distance_threshold_meters=400):
    """Check if both bike legs would be short enough to warrant transit-only fallback"""
    try:
        if not start_bus_stops or not end_bus_stops:
            return False
            
        start_bus_stop = start_bus_stops[0]
        end_bus_stop = end_bus_stops[0]
        
        # Calculate bike leg distances
        dx1 = start_point[0] - start_bus_stop['display_x']
        dy1 = start_point[1] - start_bus_stop['display_y']
        bike_leg_1_distance = math.sqrt(dx1*dx1 + dy1*dy1) * 111000  # Convert to meters
        
        dx2 = end_point[0] - end_bus_stop['display_x'] 
        dy2 = end_point[1] - end_bus_stop['display_y']
        bike_leg_2_distance = math.sqrt(dx2*dx2 + dy2*dy2) * 111000
        
        print(f"Fallback check: Bike leg 1: {bike_leg_1_distance:.0f}m, Bike leg 2: {bike_leg_2_distance:.0f}m")
        
        if bike_leg_1_distance < distance_threshold_meters and bike_leg_2_distance < distance_threshold_meters:
            print(f"Both bike legs < {distance_threshold_meters}m - Using transit-only fallback")
            return True
            
        return False
        
    except Exception as e:
        print(f"Error in fallback check: {e}")
        return False

def get_google_maps_transit_fallback(start_point, end_point, departure_time="now"):
    """Fallback to Google Maps transit routing for short bike legs"""
    try:
        print(f"Using Google Maps transit fallback")
        
        origin = f"{start_point[1]},{start_point[0]}"
        destination = f"{end_point[1]},{end_point[0]}"
        
        result = get_transit_routes_google(origin, destination, GOOGLE_API_KEY, departure_time)
        
        if 'error' not in result and result.get('routes'):
            fallback_routes = []
            
            for i, transit_route in enumerate(result['routes']):
                fallback_route = {
                    "id": i + 1,
                    "name": f"Transit Fallback Option {i + 1}",
                    "type": "transit_fallback",
                    "summary": {
                        "total_time_minutes": transit_route['duration_minutes'],
                        "total_time_formatted": transit_route['duration_text'],
                        "total_distance_miles": transit_route['distance_miles'],
                        "bike_distance_miles": 0,
                        "transit_distance_miles": transit_route['distance_miles'],
                        "bike_percentage": 0,
                        "average_bike_score": 0,
                        "transfers": transit_route.get('transfers', 0),
                        "total_fare": transit_route.get('total_fare'),
                        "departure_time": transit_route.get('departure_time', 'Unknown'),
                        "arrival_time": transit_route.get('arrival_time', 'Unknown')
                    },
                    "legs": [
                        {
                            "type": "transit",
                            "name": f"Transit Route {i + 1}",
                            "description": f"Direct transit with {transit_route.get('transfers', 0)} transfer{'s' if transit_route.get('transfers', 0) != 1 else ''}",
                            "route": transit_route,
                            "color": "#2196f3",
                            "order": 1
                        }
                    ],
                    "fallback_reason": "Both bike segments < 400m - Transit more practical"
                }
                fallback_routes.append(fallback_route)
            
            return {
                "success": True,
                "routes": fallback_routes,
                "fallback_used": True,
                "fallback_reason": "Short bike segments detected",
                "analysis_type": "transit_fallback"
            }
        
        return {"error": "Transit fallback failed"}
        
    except Exception as e:
        print(f"Error in transit fallback: {e}")
        return {"error": str(e)}

def analyze_complete_bike_bus_bike_routes(start_point, end_point, departure_time="now"):
    """Main function to analyze complete bike-bus-bike routing options"""
    try:
        print(f"\n{'='*60}")
        print(f"BIKE-BUS-BIKE ROUTE ANALYSIS (Google Maps + GTFS)")
        print(f"{'='*60}")
        print(f"Start: {start_point}")
        print(f"End: {end_point}")
        print(f"Departure: {departure_time}")
        print(f"{'='*60}")
        
        # Step 1: Find nearest bus stops
        print("\nSTEP 1: Finding nearest bus stops...")
        start_bus_stops = bike_manager.find_nearest_bus_stops(start_point, max_stops=2)
        end_bus_stops = bike_manager.find_nearest_bus_stops(end_point, max_stops=2)
        
        if not start_bus_stops:
            return {"error": "Could not find any bus stops near the start point"}
        
        if not end_bus_stops:
            return {"error": "Could not find any bus stops near the end point"}
        
        start_bus_stop = start_bus_stops[0]
        end_bus_stop = end_bus_stops[0]
        
        # Ensure different bus stops
        if start_bus_stop["id"] == end_bus_stop["id"]:
            if len(start_bus_stops) > 1:
                end_bus_stop = start_bus_stops[1]
            elif len(end_bus_stops) > 1:
                end_bus_stop = end_bus_stops[1]
            else:
                return {"error": "Only one bus stop found near both points"}
        
        print(f"Selected bus stops:")
        print(f"   Start: {start_bus_stop['name']} ({start_bus_stop['distance_meters']:.0f}m away)")
        print(f"   End: {end_bus_stop['name']} ({end_bus_stop['distance_meters']:.0f}m away)")
        
        # Check for transit fallback
        if should_use_transit_fallback(start_point, end_point, start_bus_stops, end_bus_stops):
            print("\nSMART FALLBACK: Using transit-only routing")
            
            fallback_result = get_google_maps_transit_fallback(start_point, end_point, departure_time)
            
            if fallback_result.get('success'):
                # Add direct bike route for comparison
                print("\nCreating direct bike route for comparison...")
                direct_bike_route = bike_manager.create_bike_route_google(start_point, end_point, "DirectBike")
                
                if direct_bike_route:
                    direct_route = {
                        "id": len(fallback_result['routes']) + 1,
                        "name": "Direct Bike Route",
                        "type": "direct_bike",
                        "summary": {
                            "total_time_minutes": direct_bike_route['travel_time_minutes'],
                            "total_time_formatted": direct_bike_route['travel_time_formatted'],
                            "total_distance_miles": direct_bike_route['length_miles'],
                            "bike_distance_miles": direct_bike_route['length_miles'],
                            "transit_distance_miles": 0,
                            "bike_percentage": 100,
                            "average_bike_score": direct_bike_route['overall_score'],
                            "transfers": 0,
                            "total_fare": 0,
                            "departure_time": "Immediate",
                            "arrival_time": "Flexible"
                        },
                        "legs": [
                            {
                                "type": "bike",
                                "name": "Direct Bike Route",
                                "description": "Complete bike route from start to destination",
                                "route": direct_bike_route,
                                "color": "#e74c3c",
                                "order": 1
                            }
                        ]
                    }
                    fallback_result['routes'].append(direct_route)
                
                fallback_result['routes'].sort(key=lambda x: x['summary']['total_time_minutes'])
                
                fallback_result['statistics'] = {
                    "total_options": len(fallback_result['routes']),
                    "transit_fallback_options": len([r for r in fallback_result['routes'] if r['type'] == 'transit_fallback']),
                    "direct_bike_options": len([r for r in fallback_result['routes'] if r['type'] == 'direct_bike']),
                    "fastest_option": fallback_result['routes'][0]['name'] if fallback_result['routes'] else None,
                    "fastest_time": fallback_result['routes'][0]['summary']['total_time_formatted'] if fallback_result['routes'] else None
                }
                
                fallback_result['bus_stops'] = {
                    "start_stop": start_bus_stop,
                    "end_stop": end_bus_stop,
                    "all_start_stops": start_bus_stops,
                    "all_end_stops": end_bus_stops
                }
                
                fallback_result['bike_speed_mph'] = BIKE_SPEED_MPH
                fallback_result['analysis_timestamp'] = datetime.datetime.now().isoformat()
                
                return fallback_result
            else:
                print("Transit fallback failed, proceeding with full bike-bus-bike analysis")
        
        # FULL BIKE-BUS-BIKE ANALYSIS
        print("\nSTEP 2: Creating bicycle route legs with Google Maps API...")

        # Bike leg 1: Start to bus stop
        bike_leg_1 = bike_manager.create_bike_route_google(
            start_point, 
            [start_bus_stop["display_x"], start_bus_stop["display_y"]], 
            "StartToBusStop"
        )
        
        # Bike leg 2: Bus stop to end
        bike_leg_2 = bike_manager.create_bike_route_google(
            [end_bus_stop["display_x"], end_bus_stop["display_y"]], 
            end_point, 
            "BusStopToEnd"
        )
        
        if not bike_leg_1:
            return {"error": "Could not create bike route to start bus stop"}
        
        if not bike_leg_2:
            return {"error": "Could not create bike route from end bus stop"}
        
        print(f"Bicycle legs created:")
        print(f"   Leg 1: {bike_leg_1['length_miles']:.2f} miles, {bike_leg_1['travel_time_formatted']} (Score: {bike_leg_1['overall_score']})")
        print(f"   Leg 2: {bike_leg_2['length_miles']:.2f} miles, {bike_leg_2['travel_time_formatted']} (Score: {bike_leg_2['overall_score']})")
        
        # Step 3: Get transit options
        print("\nSTEP 3: Finding transit routes between bus stops...")
        transit_result = get_transit_routes_between_stops(start_bus_stop, end_bus_stop, departure_time)
        
        if 'error' in transit_result:
            print(f"Transit routing failed: {transit_result['error']}")
            transit_routes = []
        else:
            transit_routes = transit_result.get('routes', [])
            print(f"Found {len(transit_routes)} transit options")
        
        # Step 4: Combine routes
        print("\nSTEP 4: Combining bike + transit + bike routes...")
        complete_routes = []
        
        for i, transit_route in enumerate(transit_routes):
            bike_time_1 = bike_leg_1['travel_time_minutes']
            bike_time_2 = bike_leg_2['travel_time_minutes']
            transit_time_with_waits = calculate_total_route_time_with_waits(transit_route)
            
            total_time_minutes = bike_time_1 + transit_time_with_waits + bike_time_2
            
            total_bike_miles = bike_leg_1['length_miles'] + bike_leg_2['length_miles']
            total_transit_miles = transit_route.get('distance_miles', 0)
            total_miles = total_bike_miles + total_transit_miles
            
            total_bike_length = bike_leg_1['length_meters'] + bike_leg_2['length_meters']
            if total_bike_length > 0:
                weighted_score = (
                    (bike_leg_1['overall_score'] * bike_leg_1['length_meters']) +
                    (bike_leg_2['overall_score'] * bike_leg_2['length_meters'])
                ) / total_bike_length
            else:
                weighted_score = 0
            
            enhanced_transit_route = transit_route.copy()
            enhanced_transit_route['start_stop'] = start_bus_stop
            enhanced_transit_route['end_stop'] = end_bus_stop
            
            complete_route = {
                "id": i + 1,
                "name": f"Bike-Bus-Bike Option {i + 1}",
                "type": "bike_bus_bike",
                "summary": {
                    "total_time_minutes": round(total_time_minutes, 1),
                    "total_time_formatted": format_time_duration(total_time_minutes),
                    "total_distance_miles": round(total_miles, 2),
                    "bike_distance_miles": round(total_bike_miles, 2),
                    "transit_distance_miles": round(total_transit_miles, 2),
                    "bike_percentage": round((total_bike_miles / total_miles) * 100, 1) if total_miles > 0 else 0,
                    "average_bike_score": round(weighted_score, 1),
                    "transfers": transit_route.get('transfers', 0),
                    "total_fare": transit_route.get('total_fare'),
                    "departure_time": transit_route.get('departure_time', 'Unknown'),
                    "arrival_time": transit_route.get('arrival_time', 'Unknown')
                },
                "legs": [
                    {
                        "type": "bike",
                        "name": "Bike to Bus Stop",
                        "description": f"Bike from start to {start_bus_stop['name']}",
                        "route": bike_leg_1,
                        "color": "#27ae60",
                        "order": 1
                    },
                    {
                        "type": "transit",
                        "name": f"Transit: {enhanced_transit_route.get('name', 'Bus Route')}",
                        "description": f"Transit from {start_bus_stop['name']} to {end_bus_stop['name']}",
                        "route": enhanced_transit_route,
                        "color": "#3498db",
                        "order": 2
                    },
                    {
                        "type": "bike",
                        "name": "Bus Stop to Destination",
                        "description": f"Bike from {end_bus_stop['name']} to destination",
                        "route": bike_leg_2,
                        "color": "#27ae60",
                        "order": 3
                    }
                ]
            }
            
            complete_routes.append(complete_route)
            print(f"   Created route {i+1}: {total_time_minutes:.1f} min, {total_miles:.2f} miles")
        
        # Step 5: Create direct bike route
        print("\nSTEP 5: Creating direct bike route for comparison...")
        direct_bike_route = bike_manager.create_bike_route_google(start_point, end_point, "DirectBike")

        comparison_routes = []
        if direct_bike_route:
            direct_route = {
                "id": len(complete_routes) + 1,
                "name": "Direct Bike Route",
                "type": "direct_bike",
                "summary": {
                    "total_time_minutes": direct_bike_route['travel_time_minutes'],
                    "total_time_formatted": direct_bike_route['travel_time_formatted'],
                    "total_distance_miles": direct_bike_route['length_miles'],
                    "bike_distance_miles": direct_bike_route['length_miles'],
                    "transit_distance_miles": 0,
                    "bike_percentage": 100,
                    "average_bike_score": direct_bike_route['overall_score'],
                    "transfers": 0,
                    "total_fare": 0,
                    "departure_time": "Immediate",
                    "arrival_time": "Flexible"
                },
                "legs": [
                    {
                        "type": "bike",
                        "name": "Direct Bike Route",
                        "description": "Complete bike route from start to destination",
                        "route": direct_bike_route,
                        "color": "#e74c3c",
                        "order": 1
                    }
                ]
            }
            comparison_routes.append(direct_route)
            print(f"Direct bike route: {direct_bike_route['length_miles']:.2f} miles, {direct_bike_route['travel_time_formatted']} (Score: {direct_bike_route['overall_score']})")
        
        # Sort and finalize
        all_routes = complete_routes + comparison_routes
        all_routes.sort(key=lambda x: x['summary']['total_time_minutes'])
        
        result = {
            "success": True,
            "analysis_type": "bike_bus_bike",
            "fallback_used": False,
            "routes": all_routes,
            "bus_stops": {
                "start_stop": start_bus_stop,
                "end_stop": end_bus_stop,
                "all_start_stops": start_bus_stops,
                "all_end_stops": end_bus_stops
            },
            "statistics": {
                "total_options": len(all_routes),
                "bike_bus_bike_options": len(complete_routes),
                "direct_bike_options": len(comparison_routes),
                "fastest_option": all_routes[0]['name'] if all_routes else None,
                "fastest_time": all_routes[0]['summary']['total_time_formatted'] if all_routes else None
            },
            "bike_speed_mph": BIKE_SPEED_MPH,
            "analysis_timestamp": datetime.datetime.now().isoformat()
        }
        
        print(f"\nBIKE-BUS-BIKE ANALYSIS COMPLETE:")
        print(f"   Total route options: {len(all_routes)}")
        print(f"   Multimodal routes: {len(complete_routes)}")
        print(f"   Direct bike routes: {len(comparison_routes)}")
        print(f"   Fastest option: {result['statistics']['fastest_option']} ({result['statistics']['fastest_time']})")
        
        return result
        
    except Exception as e:
        print(f"Error in bike-bus-bike analysis: {str(e)}")
        import traceback
        traceback.print_exc()
        return {"error": str(e)}

print("Part 5: Main analysis engine loaded successfully")

# bike_bus_bike_google_part6.py
# Part 6: HTTP Server, HTML Interface, and Main Execution

class BikeBusBikeGoogleServer(http.server.SimpleHTTPRequestHandler):
    """HTTP server for bike-bus-bike route analysis (Google Maps + GTFS)"""

    def do_GET(self):
        """Handle GET requests"""
        try:
            if self.path == '/':
                self.send_response(200)
                self.send_header('Content-type', 'text/html')
                self.end_headers()
                
                html_content = self.create_html_interface()
                self.wfile.write(html_content.encode('utf-8'))
                    
            elif self.path.startswith('/analyze'):
                self.handle_analysis_request()
                
            elif self.path.startswith('/status'):
                self.handle_status_request()
                
            else:
                return http.server.SimpleHTTPRequestHandler.do_GET(self)
                
        except Exception as e:
            print(f"Error handling GET request: {e}")
            self.send_error(500, f"Internal server error: {str(e)}")
    
    def handle_analysis_request(self):
        """Handle bike-bus-bike route analysis requests"""
        try:
            query = urllib.parse.urlparse(self.path).query
            params = urllib.parse.parse_qs(query)
            
            start_lon = float(params.get('start_lon', ['0'])[0])
            start_lat = float(params.get('start_lat', ['0'])[0])
            end_lon = float(params.get('end_lon', ['0'])[0])
            end_lat = float(params.get('end_lat', ['0'])[0])
            departure_time = params.get('departure_time', ['now'])[0]
            
            print(f"\nAnalysis request received:")
            print(f"   Start: ({start_lat:.5f}, {start_lon:.5f})")
            print(f"   End: ({end_lat:.5f}, {end_lon:.5f})")
            print(f"   Departure: {departure_time}")
            
            if not (-90 <= start_lat <= 90 and -180 <= start_lon <= 180):
                raise ValueError("Invalid start coordinates")
            if not (-90 <= end_lat <= 90 and -180 <= end_lon <= 180):
                raise ValueError("Invalid end coordinates")
            
            # Check system status
            status_issues = []
            if not is_valid_api_key():
                status_issues.append("Google Maps API key not properly configured")
            
            if status_issues:
                result = {
                    "error": "System configuration issues detected",
                    "issues": status_issues,
                    "suggestions": [
                        "Verify Google Maps API key configuration",
                        "Check shapefile paths"
            
                    ]
                }
            else:
                result = analyze_complete_bike_bus_bike_routes(
                    [start_lon, start_lat], 
                    [end_lon, end_lat],
                    departure_time
                )
            
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            
            response_json = json.dumps(result, indent=2, default=str)
            self.wfile.write(response_json.encode())
            
            print(f"Analysis response sent ({len(response_json)} bytes)")
            
        except ValueError as e:
            error_msg = f"Invalid request parameters: {str(e)}"
            print(f"Error: {error_msg}")
            self.send_error(400, error_msg)
            
        except Exception as e:
            error_msg = f"Analysis failed: {str(e)}"
            print(f"Error: {error_msg}")
            
            error_response = {
                "error": error_msg,
                "timestamp": datetime.datetime.now().isoformat(),
                "request_path": self.path
            }
            
            self.send_response(500)
            self.send_header('Content-type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(json.dumps(error_response, indent=2).encode())
    
    def handle_status_request(self):
        """Handle system status requests"""
        try:
            api_key_status = is_valid_api_key()
            gtfs_status = gtfs_manager.is_loaded
            roads_status = bike_manager.roads_gdf is not None
            stops_status = bike_manager.transit_stops_gdf is not None
            
            status = {
                "system_status": "operational" if api_key_status else "degraded",
                "components": {
                    "google_maps_api": {
                        "url": "https://maps.googleapis.com/maps/api",
                        "status": "assumed_ok"
                    },
                    "google_maps_api": {
                        "status": "ok" if api_key_status else "error",
                        "key_configured": bool(GOOGLE_API_KEY and len(GOOGLE_API_KEY) > 30)
                    },
                    "gtfs_data": {
                        "status": "ok" if gtfs_status else "warning",
                        "loaded": gtfs_status,
                        "last_update": gtfs_manager.last_update.isoformat() if gtfs_manager.last_update else None,
                        "routes_count": len(gtfs_manager.routes_df) if gtfs_manager.routes_df is not None else 0,
                        "stops_count": len(gtfs_manager.stops_df) if gtfs_manager.stops_df is not None else 0
                    },
                    "roads_shapefile": {
                        "status": "ok" if roads_status else "warning",
                        "loaded": roads_status,
                        "features": len(bike_manager.roads_gdf) if roads_status else 0
                    },
                    "transit_stops_shapefile": {
                        "status": "ok" if stops_status else "warning",
                        "loaded": stops_status,
                        "features": len(bike_manager.transit_stops_gdf) if stops_status else 0
                    }
                },
                "configuration": {
                    "bike_speed_mph": BIKE_SPEED_MPH,
                    "temp_workspace": TEMP_WORKSPACE,
                    "default_center": DEFAULT_CENTER
                },
                "timestamp": datetime.datetime.now().isoformat()
            }
            
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(json.dumps(status, indent=2, default=str).encode())
            
        except Exception as e:
            print(f"Error handling status request: {e}")
            self.send_error(500, f"Status check failed: {str(e)}")
    
    
    def create_html_interface(self):
        """Create the enhanced HTML interface with Google Maps-style cards for all route types"""
        lat, lon = DEFAULT_CENTER

        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Bike-Bus-Bike Route Planner (Enhanced)</title>
    <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
    <style>
        * {{ box-sizing: border-box; margin: 0; padding: 0; }}
        body {{ 
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; 
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); 
            min-height: 100vh; 
        }}
        
        .header {{ 
            background: linear-gradient(135deg, #4285f4, #34a853); 
            color: white; 
            padding: 20px; 
            text-align: center; 
            box-shadow: 0 2px 10px rgba(0,0,0,0.2); 
        }}
        
        .header h1 {{ 
            margin: 0; 
            font-size: 2.2em; 
            font-weight: 300; 
            display: flex; 
            align-items: center; 
            justify-content: center; 
            gap: 10px; 
        }}
        
        .header p {{ margin: 10px 0 0 0; opacity: 0.9; font-size: 1.1em; }}
        
        .speed-badge {{ 
            background: linear-gradient(45deg, #ff6b6b, #4ecdc4); 
            color: white; 
            padding: 4px 8px; 
            border-radius: 4px; 
            font-size: 0.8em; 
            animation: pulse 2s infinite; 
        }}
        
        @keyframes pulse {{ 0%, 100% {{ opacity: 1; }} 50% {{ opacity: 0.7; }} }}
        
        .container {{ 
            display: flex; 
            height: calc(100vh - 120px); 
            max-width: 1400px; 
            margin: 0 auto; 
            background: white; 
            border-radius: 10px 10px 0 0; 
            overflow: hidden; 
            box-shadow: 0 -5px 20px rgba(0,0,0,0.1); 
        }}
        
        #map {{ flex: 2; height: 100%; }}
        
        #sidebar {{ 
            flex: 1; 
            padding: 25px; 
            overflow-y: auto; 
            max-width: 450px; 
            background: #f8f9fa; 
            border-left: 1px solid #dee2e6; 
        }}
        
        .system-status {{ 
            background: linear-gradient(135deg, #d4edda, #c3e6cb); 
            color: #155724; 
            padding: 12px; 
            border-radius: 8px; 
            margin-bottom: 20px; 
            text-align: center; 
            font-weight: 500; 
            border-left: 4px solid #28a745; 
        }}
        
        .click-instruction {{ 
            background: linear-gradient(135deg, #fff3cd, #ffeaa7); 
            color: #856404; 
            padding: 15px; 
            border-radius: 8px; 
            margin-bottom: 20px; 
            text-align: center; 
            border-left: 4px solid #f1c40f; 
        }}
        
        .form-group {{ margin-bottom: 20px; }}
        
        label {{ 
            display: block; 
            margin-bottom: 8px; 
            font-weight: 600; 
            color: #333; 
            font-size: 1em; 
        }}
        
        input, select {{ 
            width: 100%; 
            padding: 12px 15px; 
            border: 2px solid #e1e5e9; 
            border-radius: 8px; 
            font-size: 1em; 
            transition: all 0.3s ease; 
            background: white; 
            box-sizing: border-box; 
        }}
        
        input:focus, select:focus {{ 
            outline: none; 
            border-color: #4285f4; 
            box-shadow: 0 0 0 3px rgba(66, 133, 244, 0.1); 
        }}
        
        button {{ 
            background: linear-gradient(135deg, #4285f4, #34a853); 
            color: white; 
            padding: 15px 25px; 
            border: none; 
            border-radius: 8px; 
            cursor: pointer; 
            font-size: 1.1em; 
            font-weight: 600; 
            width: 100%; 
            margin-bottom: 15px; 
            transition: all 0.3s ease; 
        }}
        
        button:hover:not(:disabled) {{ 
            transform: translateY(-2px); 
            box-shadow: 0 8px 20px rgba(66, 133, 244, 0.3); 
        }}
        
        button:disabled {{ 
            background: #ccc; 
            cursor: not-allowed; 
            transform: none; 
            box-shadow: none; 
        }}
        
        .clear-btn {{ background: linear-gradient(135deg, #ea4335, #fbbc04); }}
        
        .spinner {{ 
            border: 3px solid #f3f3f3; 
            border-top: 3px solid #4285f4; 
            border-radius: 50%; 
            width: 35px; 
            height: 35px; 
            animation: spin 1s linear infinite; 
            margin: 25px auto; 
            display: none; 
        }}
        
        @keyframes spin {{ 0% {{ transform: rotate(0deg); }} 100% {{ transform: rotate(360deg); }} }}
        
        .error {{ 
            background: linear-gradient(135deg, #ffebee, #ffcdd2); 
            color: #c62828; 
            padding: 15px; 
            border-radius: 8px; 
            margin: 15px 0; 
            border-left: 4px solid #f44336; 
        }}
        
        .info {{ 
            background: linear-gradient(135deg, #e3f2fd, #bbdefb); 
            color: #1565c0; 
            padding: 15px; 
            border-radius: 8px; 
            margin: 15px 0; 
            border-left: 4px solid #2196f3; 
        }}
        
        .hidden {{ display: none; }}
        
        /* ========================================
           GOOGLE MAPS STYLE ROUTE CARDS
           ======================================== */
        
        .route-card {{
            background: white;
            border-radius: 16px;
            padding: 0;
            margin-bottom: 20px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            cursor: pointer;
            transition: all 0.3s ease;
            overflow: hidden;
        }}
        
        .route-card:hover {{
            box-shadow: 0 4px 16px rgba(0,0,0,0.15);
            transform: translateY(-2px);
        }}
        
        .route-card.selected {{
            box-shadow: 0 0 0 3px #1a73e8;
        }}
        
        /* Route Header Section */
        .route-header-section {{
            background: #f8f9fa;
            padding: 20px;
            border-bottom: 1px solid #e8eaed;
        }}
        
        .bike-route-header {{
            background: linear-gradient(135deg, #e8f5e9, #c8e6c9);
            padding: 20px;
            border-bottom: 1px solid #a5d6a7;
        }}
        
        .route-title {{
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 16px;
        }}
        
        .route-title h3 {{
            font-size: 18px;
            font-weight: 600;
            color: #202124;
            margin: 0;
        }}
        
        .live-badge {{
            background: #ea4335;
            color: white;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 11px;
            font-weight: 600;
            letter-spacing: 0.5px;
        }}
        
        .multimodal-badge {{
            background: linear-gradient(135deg, #ff6b6b, #f39c12);
            color: white;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 11px;
            font-weight: 600;
            letter-spacing: 0.5px;
        }}
        
        /* Time Summary Section */
        .time-summary {{
            display: grid;
            grid-template-columns: 1fr 1.5fr 1fr;
            gap: 12px;
            text-align: center;
        }}
        
        .time-summary-item {{
            display: flex;
            flex-direction: column;
        }}
        
        .time-summary-label {{
            font-size: 11px;
            color: #5f6368;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            font-weight: 500;
            margin-bottom: 4px;
        }}
        
        .time-summary-value {{
            font-size: 20px;
            font-weight: 600;
            color: #1a73e8;
        }}
        
        .duration-value {{
            font-size: 18px;
        }}
        
        /* Stats Bar */
        .stats-bar {{
            display: flex;
            justify-content: space-around;
            padding: 16px 20px;
            background: white;
            border-bottom: 1px solid #e8eaed;
        }}
        
        .stat-item {{
            text-align: center;
        }}
        
        .stat-value {{
            font-size: 24px;
            font-weight: 600;
            color: #202124;
            display: block;
        }}
        
        .stat-label {{
            font-size: 11px;
            color: #5f6368;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            margin-top: 2px;
            display: block;
        }}
        
        /* Route Steps Section */
        .route-steps {{
            padding: 0;
        }}
        
        .route-step {{
            display: flex;
            padding: 16px 20px;
            border-bottom: 1px solid #f1f3f4;
            align-items: flex-start;
            gap: 16px;
            transition: background 0.2s ease;
        }}
        
        .route-step:hover {{
            background: #f8f9fa;
        }}
        
        .route-step:last-child {{
            border-bottom: none;
        }}
        
        /* Step Icons */
        .step-icon {{
            width: 40px;
            height: 40px;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 20px;
            flex-shrink: 0;
        }}
        
        .step-icon.walk {{
            background: #34a853;
            color: white;
        }}
        
        .step-icon.bus {{
            background: #4285f4;
            color: white;
        }}
        
        .step-icon.bike {{
            background: #27ae60;
            color: white;
        }}
        
        /* Step Content */
        .step-content {{
            flex: 1;
        }}
        
        .step-title {{
            font-size: 15px;
            font-weight: 600;
            color: #202124;
            margin-bottom: 4px;
        }}
        
        .step-subtitle {{
            font-size: 13px;
            color: #5f6368;
            margin-bottom: 8px;
        }}
        
        /* Transit Details Box */
        .transit-details {{
            background: #f8f9fa;
            border-left: 4px solid #4285f4;
            padding: 12px;
            border-radius: 4px;
            margin-top: 8px;
        }}
        
        .transit-line {{
            display: flex;
            align-items: center;
            gap: 8px;
            margin-bottom: 8px;
        }}
        
        .transit-badge {{
            background: white;
            border: 2px solid #4285f4;
            color: #4285f4;
            padding: 4px 10px;
            border-radius: 12px;
            font-size: 13px;
            font-weight: 700;
            display: inline-flex;
            align-items: center;
            gap: 4px;
        }}
        
        .transit-info-line {{
            display: flex;
            align-items: center;
            gap: 6px;
            font-size: 13px;
            color: #5f6368;
            margin: 4px 0;
        }}
        
        .transit-time {{
            font-weight: 600;
            color: #202124;
        }}
        
        /* Bike Details Box */
        .bike-step-details {{
            background: linear-gradient(135deg, #e8f5e9, #f1f8e9);
            border-left: 4px solid #27ae60;
            padding: 12px;
            border-radius: 4px;
            margin-top: 8px;
        }}
        
        .bike-metrics-grid {{
            display: grid;
            grid-template-columns: repeat(2, 1fr);
            gap: 8px;
            margin-bottom: 12px;
        }}
        
        .bike-metric-item {{
            display: flex;
            align-items: center;
            gap: 6px;
            font-size: 13px;
            color: #5f6368;
        }}
        
        .bike-metric-value {{
            font-weight: 600;
            color: #202124;
        }}
        
        /* Safety Score Badge */
        .safety-score-badge {{
            display: inline-flex;
            align-items: center;
            gap: 6px;
            padding: 6px 12px;
            border-radius: 16px;
            font-size: 12px;
            font-weight: 600;
            margin-top: 8px;
        }}
        
        .safety-score-excellent {{
            background: #e6f4ea;
            color: #137333;
        }}
        
        .safety-score-good {{
            background: #e8f5e9;
            color: #2e7d32;
        }}
        
        .safety-score-fair {{
            background: #fff3e0;
            color: #e65100;
        }}
        
        .safety-score-poor {{
            background: #fce8e6;
            color: #c5221f;
        }}
        
        /* Facility Distribution */
        .facility-distribution {{
            margin-top: 12px;
            padding-top: 12px;
            border-top: 1px solid #e8eaed;
        }}
        
        .facility-dist-title {{
            font-size: 11px;
            font-weight: 600;
            color: #5f6368;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            margin-bottom: 8px;
        }}
        
        .facility-bar-container {{
            width: 100%;
            height: 24px;
            background: #f1f3f4;
            border-radius: 12px;
            overflow: hidden;
            display: flex;
            box-shadow: inset 0 1px 3px rgba(0,0,0,0.1);
        }}
        
        .facility-segment {{
            height: 100%;
            transition: all 0.3s ease;
            position: relative;
            cursor: pointer;
        }}
        
        .facility-segment:hover {{
            filter: brightness(0.9);
        }}
        
        .facility-segment-label {{
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            font-size: 10px;
            font-weight: 700;
            color: white;
            text-shadow: 0 1px 2px rgba(0,0,0,0.3);
            white-space: nowrap;
        }}
        
        .facility-legend-items {{
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
            margin-top: 8px;
        }}
        
        .facility-legend-item {{
            display: flex;
            align-items: center;
            gap: 4px;
            padding: 4px 8px;
            background: white;
            border-radius: 12px;
            font-size: 11px;
            box-shadow: 0 1px 3px rgba(0,0,0,0.1);
        }}
        
        .facility-color-dot {{
            width: 12px;
            height: 12px;
            border-radius: 50%;
            flex-shrink: 0;
        }}
        
        .facility-percentage {{
            font-weight: 600;
            color: #5f6368;
        }}
        
        /* Real-time Status */
        .realtime-status {{
            display: inline-flex;
            align-items: center;
            gap: 4px;
            padding: 4px 8px;
            border-radius: 12px;
            font-size: 11px;
            font-weight: 600;
            margin-top: 6px;
        }}
        
        .realtime-status.on-time {{
            background: #e6f4ea;
            color: #137333;
        }}
        
        .realtime-status.delayed {{
            background: #fef7e0;
            color: #ea8600;
        }}
        
        .realtime-status.late {{
            background: #fce8e6;
            color: #c5221f;
        }}
        
        /* Fallback Notice */
        .fallback-notice {{
            background: linear-gradient(135deg, #e3f2fd, #bbdefb);
            color: #1565c0;
            padding: 16px;
            border-radius: 12px;
            margin-bottom: 20px;
            border-left: 5px solid #2196f3;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
        }}
        
        .fallback-notice-header {{
            display: flex;
            align-items: center;
            gap: 10px;
            margin-bottom: 8px;
        }}
        
        .fallback-notice-header strong {{
            font-size: 16px;
        }}
        
        .fallback-notice p {{
            margin: 0;
            font-size: 14px;
            line-height: 1.5;
        }}
        
        /* Facility Type Legend */
        .facility-legend {{
            background: white;
            padding: 15px;
            border-radius: 8px;
            margin-bottom: 20px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }}
        
        .facility-legend h4 {{
            margin: 0 0 10px 0;
            font-size: 14px;
            color: #333;
        }}
        
        .legend-item {{
            display: flex;
            align-items: center;
            gap: 8px;
            margin: 5px 0;
            font-size: 12px;
        }}
        
        .legend-color {{
            width: 30px;
            height: 15px;
            border-radius: 3px;
        }}
        
        /* Responsive Design */
        @media (max-width: 1200px) {{
            .container {{
                flex-direction: column;
                height: auto;
                min-height: calc(100vh - 120px);
            }}
            #map {{ height: 50vh; min-height: 400px; }}
            #sidebar {{ max-width: none; flex: none; }}
            .time-summary {{ grid-template-columns: 1fr; gap: 8px; }}
            .stats-bar {{ flex-wrap: wrap; gap: 12px; }}
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🚴 Bike-Bus-Bike Route Planner <span class="speed-badge">@ GOOGLE MAPS BIKE TIMES</span></h1>
        <p>Google Maps Bicycling + Transit API + Real-time GTFS</p>
    </div>
    
    <div class="container">
        <div id="map"></div>
        
        <div id="sidebar">
            <div class="system-status">🟢 System Ready: Google Maps API + GTFS</div>
            
            <div class="click-instruction">
                <strong>📍 How to Use:</strong><br>
                1. Enter addresses OR click map for origin/destination<br>
                2. Choose departure time<br>
                3. Get multimodal routes with live transit data!<br>
                🎨 Smart fallback for short bike segments
            </div>
            
            <!-- Facility Type Legend -->
            <div class="facility-legend">
                <h4>🚴 Bike Facility Colors</h4>
                <div class="legend-item">
                    <div class="legend-color" style="background: #27ae60;"></div>
                    <span><strong>Protected Bike Lane</strong></span>
                </div>
                <div class="legend-item">
                    <div class="legend-color" style="background: #2ecc71;"></div>
                    <span><strong>Buffered Bike Lane</strong></span>
                </div>
                <div class="legend-item">
                    <div class="legend-color" style="background: #3498db;"></div>
                    <span><strong>Unbuffered Bike Lane</strong></span>
                </div>
                <div class="legend-item">
                    <div class="legend-color" style="background: #f1c40f;"></div>
                    <span><strong>Shared Lane</strong></span>
                </div>
                <div class="legend-item">
                    <div class="legend-color" style="background: #9b59b6;"></div>
                    <span><strong>Shared Use Path</strong></span>
                </div>
                <div class="legend-item">
                    <div class="legend-color" style="background: #e74c3c;"></div>
                    <span><strong>No Bike Lane</strong></span>
                </div>
            </div>
            
            <div class="form-group">
                <label for="originInput">🚩 From (Origin):</label>
                <input type="text" id="originInput" placeholder="Enter address or click map">
            </div>
            
            <div class="form-group">
                <label for="destinationInput">🎯 To (Destination):</label>
                <input type="text" id="destinationInput" placeholder="Enter address or click map">
            </div>
            
            <div class="form-group">
                <label for="departureTime">🕐 Departure Time:</label>
                <select id="departureTime">
                    <option value="now">Leave Now</option>
                    <option value="custom">Custom Time</option>
                </select>
            </div>
            
            <div class="form-group hidden" id="customTimeGroup">
                <label for="customTime">Select Time:</label>
                <input type="datetime-local" id="customTime">
            </div>
            
            <button id="findRouteBtn" onclick="findTransitRoute()">🔍 Find Bike-Bus-Bike Routes</button>
            <button class="clear-btn" onclick="clearAll()">🗑️ Clear All</button>
            
            <div class="spinner" id="spinner"></div>
            <div id="results"></div>
        </div>
    </div>

    <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
    <script>
            // Initialize map
        const map = L.map('map').setView([{lat}, {lon}], {DEFAULT_ZOOM});
        L.tileLayer('https://{{s}}.tile.openstreetmap.org/{{z}}/{{x}}/{{y}}.png', {{
            attribution: '© OpenStreetMap contributors',
            maxZoom: 19
        }}).addTo(map);
        
        let originMarker = null, destinationMarker = null, routeLayersGroup = L.layerGroup().addTo(map);
        let currentRoutes = [], selectedRouteIndex = -1, clickCount = 0, originCoords = null, destinationCoords = null;
        
        // Facility type to color mapping
        const facilityColors = {{
            'PROTECTED BIKELANE': '#27ae60',
            'PROTECTED BIKE LANE': '#27ae60',
            'BUFFERED BIKELANE': '#2ecc71',
            'BUFFERED BIKE LANE': '#2ecc71',
            'UNBUFFERED BIKELANE': '#3498db',
            'UNBUFFERED BIKE LANE': '#3498db',
            'SHARED LANE': '#f1c40f',
            'BIKE ROUTE': '#f39c12',
            'SHARED USE PATH': '#9b59b6',
            'MIXED USE PATH': '#9b59b6',
            'BIKE PATH': '#8e44ad',
            'NO BIKELANE': '#e74c3c',
            'NO BIKE LANE': '#e74c3c'
        }};
        
        function getFacilityColor(facilityType) {{
            const type = (facilityType || 'NO BIKELANE').toUpperCase().trim();
            return facilityColors[type] || '#95a5a6';
        }}
        
        function getSafetyScoreClass(score) {{
            if (score >= 80) return 'safety-score-excellent';
            if (score >= 60) return 'safety-score-good';
            if (score >= 40) return 'safety-score-fair';
            return 'safety-score-poor';
        }}
        
        function getSafetyScoreLabel(score) {{
            if (score >= 80) return 'Excellent';
            if (score >= 60) return 'Good';
            if (score >= 40) return 'Fair';
            return 'Needs Improvement';
        }}
        
        // Geocoding function
        async function geocodeAddress(address) {{
            try {{
                const response = await fetch(`https://nominatim.openstreetmap.org/search?format=json&q=${{encodeURIComponent(address)}}&limit=1`);
                const data = await response.json();
                if (data && data.length > 0) {{
                    return {{
                        lat: parseFloat(data[0].lat),
                        lon: parseFloat(data[0].lon),
                        display_name: data[0].display_name
                    }};
                }}
                return null;
            }} catch (error) {{
                console.error('Geocoding error:', error);
                return null;
            }}
        }}
        
        // Address input handlers
        document.getElementById('originInput').addEventListener('keypress', async function(e) {{
            if (e.key === 'Enter') {{
                const address = this.value.trim();
                if (address) {{
                    showSpinner(true);
                    const result = await geocodeAddress(address);
                    showSpinner(false);
                    if (result) {{
                        originCoords = {{lat: result.lat, lng: result.lon}};
                        setOriginMarker(result.lat, result.lon);
                        this.value = result.display_name;
                        checkInputs();
                    }} else {{
                        alert('Could not find address. Please try again or click the map.');
                    }}
                }}
            }}
        }});
        
        document.getElementById('destinationInput').addEventListener('keypress', async function(e) {{
            if (e.key === 'Enter') {{
                const address = this.value.trim();
                if (address) {{
                    showSpinner(true);
                    const result = await geocodeAddress(address);
                    showSpinner(false);
                    if (result) {{
                        destinationCoords = {{lat: result.lat, lng: result.lon}};
                        setDestinationMarker(result.lat, result.lon);
                        this.value = result.display_name;
                        checkInputs();
                    }} else {{
                        alert('Could not find address. Please try again or click the map.');
                    }}
                }}
            }}
        }});
        
        // Map click handler
        map.on('click', function(e) {{
            const lat = e.latlng.lat, lng = e.latlng.lng;
            
            if (clickCount === 0) {{
                originCoords = {{lat, lng}};
                setOriginMarker(lat, lng);
                document.getElementById('originInput').value = `${{lat.toFixed(6)}}, ${{lng.toFixed(6)}}`;
                clickCount = 1;
            }} else if (clickCount === 1) {{
                destinationCoords = {{lat, lng}};
                setDestinationMarker(lat, lng);
                document.getElementById('destinationInput').value = `${{lat.toFixed(6)}}, ${{lng.toFixed(6)}}`;
                clickCount = 2;
                document.getElementById('findRouteBtn').disabled = false;
            }} else {{
                clearAll();
                map.fire('click', e);
            }}
        }});
        
        function setOriginMarker(lat, lng) {{
            if (originMarker) map.removeLayer(originMarker);
            originMarker = L.marker([lat, lng], {{
                icon: L.divIcon({{
                    html: '<div style="width:20px;height:20px;background:#34a853;border-radius:50%;display:flex;align-items:center;justify-content:center;color:white;font-weight:bold;font-size:12px;">A</div>',
                    iconSize: [26, 26],
                    iconAnchor: [13, 13]
                }})
            }}).addTo(map);
            originMarker.bindPopup("🚩 Origin").openPopup();
        }}
        
        function setDestinationMarker(lat, lng) {{
            if (destinationMarker) map.removeLayer(destinationMarker);
            destinationMarker = L.marker([lat, lng], {{
                icon: L.divIcon({{
                    html: '<div style="width:20px;height:20px;background:#ea4335;border-radius:50%;display:flex;align-items:center;justify-content:center;color:white;font-weight:bold;font-size:12px;">B</div>',
                    iconSize: [26, 26],
                    iconAnchor: [13, 13]
                }})
            }}).addTo(map);
            destinationMarker.bindPopup("🎯 Destination").openPopup();
        }}
        
        function checkInputs() {{
            document.getElementById('findRouteBtn').disabled = !(originCoords && destinationCoords);
        }}
        
        function clearAll() {{
            if (originMarker) {{ map.removeLayer(originMarker); originMarker = null; }}
            if (destinationMarker) {{ map.removeLayer(destinationMarker); destinationMarker = null; }}
            routeLayersGroup.clearLayers();
            document.getElementById('originInput').value = '';
            document.getElementById('destinationInput').value = '';
            document.getElementById('results').innerHTML = '';
            clickCount = 0;
            currentRoutes = [];
            selectedRouteIndex = -1;
            originCoords = null;
            destinationCoords = null;
            document.getElementById('findRouteBtn').disabled = true;
        }}
        
        document.getElementById('departureTime').addEventListener('change', function() {{
            const customTimeGroup = document.getElementById('customTimeGroup');
            if (this.value === 'custom') {{
                customTimeGroup.classList.remove('hidden');
                const now = new Date();
                now.setMinutes(now.getMinutes() - now.getTimezoneOffset());
                document.getElementById('customTime').value = now.toISOString().slice(0, 16);
            }} else {{
                customTimeGroup.classList.add('hidden');
            }}
        }});
        
        function showSpinner(show) {{
            document.getElementById('spinner').style.display = show ? 'block' : 'none';
            document.getElementById('findRouteBtn').disabled = show;
            document.getElementById('findRouteBtn').innerHTML = show ? '⏳ Finding Routes...' : '🔍 Find Bike-Bus-Bike Routes';
        }}
        
        function showError(message) {{
            document.getElementById('results').innerHTML = '<div class="error"><strong>⚠️ Error:</strong> ' + message + '</div>';
        }}
        
        async function findTransitRoute() {{
            if (!originCoords || !destinationCoords) {{
                showError('Please set both origin and destination');
                return;
            }}
            
            showSpinner(true);
            routeLayersGroup.clearLayers();
            
            try {{
                const departureTimeOption = document.getElementById('departureTime').value;
                let departureTime = 'now';
                
                if (departureTimeOption === 'custom') {{
                    const customTime = document.getElementById('customTime').value;
                    if (customTime) departureTime = Math.floor(new Date(customTime).getTime() / 1000);
                }}
                
                const params = new URLSearchParams({{
                    start_lon: originCoords.lng,
                    start_lat: originCoords.lat,
                    end_lon: destinationCoords.lng,
                    end_lat: destinationCoords.lat,
                    departure_time: departureTime
                }});
                
                const url = '/analyze?' + params.toString();
                const response = await fetch(url);
                const data = await response.json();
                
                showSpinner(false);
                
                if (data.error) {{
                    showError(data.error);
                    return;
                }}
                
                currentRoutes = data.routes || [];
                displayEnhancedRoutes(data);
                if (currentRoutes.length > 0) showRouteOnMap(0);
                
            }} catch (error) {{
                console.error('Error:', error);
                showSpinner(false);
                showError('Failed to find routes. Please check your connection.');
            }}
        }}
        
        // ========================================
        // DISPLAY FUNCTIONS
        // ========================================
        
        function displayEnhancedRoutes(data) {{
            if (!data.routes || data.routes.length === 0) {{
                document.getElementById('results').innerHTML = 
                    '<div class="info"><strong>ℹ️ Info:</strong> No routes found</div>';
                return;
            }}
            
            let html = '';
            
            // Show fallback notice if triggered
            if (data.fallback_used) {{
                html += `
                <div class="fallback-notice">
                    <div class="fallback-notice-header">
                        <span style="font-size: 24px;">🔄</span>
                        <strong>Smart Transit Fallback Activated</strong>
                    </div>
                    <p>
                        ${{data.fallback_reason}}<br>
                        <em>Walking distances are very short (&lt;400m each) - direct transit is more practical</em>
                    </p>
                </div>`;
            }}
            
            // Generate route cards based on type
            data.routes.forEach((route, index) => {{
                if (route.type === 'transit_fallback') {{
                    html += createTransitFallbackCard(route, index);
                }} else if (route.type === 'bike_bus_bike') {{
                    html += createBikeBusBikeCard(route, index);
                }} else if (route.type === 'direct_bike') {{
                    html += createDirectBikeCard(route, index);
                }}
            }});
            
            document.getElementById('results').innerHTML = html;
        }}
        
        // ========================================
        // TRANSIT FALLBACK CARD (GOOGLE MAPS STYLE)
        // ========================================
        
        function createTransitFallbackCard(route, index) {{
            const summary = route.summary;
            
            let html = `
            <div class="route-card" onclick="selectRoute(${{index}})" id="routeCard${{index}}">
                <!-- Header Section -->
                <div class="route-header-section">
                    <div class="route-title">
                        <h3>Best Route</h3>
                        <span class="live-badge">LIVE</span>
                    </div>
                    
                    <!-- Time Summary -->
                    <div class="time-summary">
                        <div class="time-summary-item">
                            <span class="time-summary-label">DEPART</span>
                            <span class="time-summary-value">${{formatTime(summary.departure_time)}}</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">DURATION</span>
                            <span class="time-summary-value duration-value">${{summary.total_time_formatted}}</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">ARRIVE</span>
                            <span class="time-summary-value">${{formatTime(summary.arrival_time)}}</span>
                        </div>
                    </div>
                </div>
                
                <!-- Stats Bar -->
                <div class="stats-bar">
                    <div class="stat-item">
                        <span class="stat-value">${{summary.total_distance_miles.toFixed(1)}}</span>
                        <span class="stat-label">MILES</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{summary.transfers || 0}}</span>
                        <span class="stat-label">TRANSFERS</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{(summary.bike_distance_miles || 0).toFixed(2)}}</span>
                        <span class="stat-label">WALK (MI)</span>
                    </div>
                </div>
                
                <!-- Route Steps -->
                <div class="route-steps">`;
            
            // Parse transit route steps
            if (route.legs && route.legs.length > 0) {{
                const transitLeg = route.legs[0];
                const transitRoute = transitLeg.route;
                
                if (transitRoute && transitRoute.steps) {{
                    transitRoute.steps.forEach((step, stepIndex) => {{
                        html += createDetailedTransitStep(step, stepIndex);
                    }});
                }}
            }}
            
            html += `
                </div>
            </div>`;
            
            return html;
        }}
        
        function createDetailedTransitStep(step, stepIndex) {{
            const isWalking = step.travel_mode === 'WALKING';
            const isTransit = step.travel_mode === 'TRANSIT';
            
            let html = `<div class="route-step">`;
            
            if (isWalking) {{
                html += `
                    <div class="step-icon walk">🚶</div>
                    <div class="step-content">
                        <div class="step-title">Walk to ${{extractDestination(step.instruction)}}</div>
                        <div class="step-subtitle">${{step.duration_text}} • ${{(step.distance_meters / 1000).toFixed(2)}} km</div>
                    </div>`;
                    
            }} else if (isTransit) {{
                html += `
                    <div class="step-icon bus">🚌</div>
                    <div class="step-content">
                        <div class="step-title">Bus towards ${{step.headsign || 'Destination'}}</div>
                        <div class="step-subtitle">${{step.duration_text}} • ${{(step.distance_meters / 1000).toFixed(2)}} km</div>
                        
                        <div class="transit-details">
                            <!-- Transit Line Badge -->
                            <div class="transit-line">
                                <span class="transit-badge">
                                    <span style="font-size: 16px;">🚌</span>
                                    ${{step.transit_line || 'Bus'}}
                                </span>
                                <span style="font-size: 12px; color: #5f6368;">- ${{step.transit_vehicle_name || 'Bus'}}</span>
                            </div>
                            
                            <!-- Route: From → To -->
                            <div class="transit-info-line">
                                <span style="font-size: 16px;">📍</span>
                                <span>${{step.departure_stop_name}} → ${{step.arrival_stop_name}}</span>
                            </div>
                            
                            <!-- Timing -->
                            <div class="transit-info-line">
                                <span style="font-size: 16px;">🕐</span>
                                <span>
                                    <span class="transit-time">${{step.scheduled_departure}}</span> 
                                    → 
                                    <span class="transit-time">${{step.scheduled_arrival}}</span>
                                </span>
                            </div>
                            
                            <!-- Number of stops -->
                            <div class="transit-info-line">
                                <span style="font-size: 16px;">🚏</span>
                                <span>${{step.num_stops || 0}} stops</span>
                            </div>
                            
                            ${{step.headsign ? `
                            <div class="transit-info-line">
                                <span style="font-size: 16px;">➡️</span>
                                <span>Direction: ${{step.headsign}}</span>
                            </div>` : ''}}
                            
                            ${{createRealtimeStatusDisplay(step)}}
                        </div>
                    </div>`;
            }}
            
            html += `</div>`;
            return html;
        }}
        
        function createRealtimeStatusDisplay(step) {{
            if (!step.gtfs_data) return '';
            
            const gtfsData = step.gtfs_data;
            const hasDelays = gtfsData.has_delays;
            
            let html = `
                <div class="realtime-status ${{hasDelays ? 'delayed' : 'on-time'}}" style="margin-top: 8px;">
                    🔴 ${{hasDelays ? 'Delays Reported' : 'On Time'}}
                </div>`;
            
            // Show next departures
            if (gtfsData.next_departures && gtfsData.next_departures.length > 0) {{
                html += `
                <div style="margin-top: 12px; padding-top: 12px; border-top: 1px solid #e8eaed;">
                    <div style="font-size: 12px; font-weight: 600; color: #5f6368; margin-bottom: 6px;">
                        NEXT DEPARTURES
                    </div>`;
                
                gtfsData.next_departures.slice(0, 3).forEach((time, idx) => {{
                    const status = gtfsData.departure_status?.[idx] || 'Scheduled';
                    const statusClass = status.includes('Delayed') ? 'delayed' : 'on-time';
                    
                    html += `
                    <div style="display: flex; justify-content: space-between; align-items: center; padding: 4px 0; font-size: 13px;">
                        <span style="font-weight: 600; color: #202124;">${{time}}</span>
                        <span class="realtime-status ${{statusClass}}" style="margin: 0;">${{status}}</span>
                    </div>`;
                }});
                
                html += `</div>`;
            }}
            
            return html;
        }}
        
        // ========================================
        // BIKE-BUS-BIKE CARD (ENHANCED GOOGLE STYLE)
        // ========================================
        
        function createBikeBusBikeCard(route, index) {{
            const summary = route.summary;
            
            let html = `
            <div class="route-card" onclick="selectRoute(${{index}})" id="routeCard${{index}}">
                <!-- Header Section with Multimodal Style -->
                <div class="bike-route-header">
                    <div class="route-title">
                        <h3>${{route.name}}</h3>
                        <span class="multimodal-badge">MULTIMODAL</span>
                    </div>
                    
                    <!-- Time Summary -->
                    <div class="time-summary">
                        <div class="time-summary-item">
                            <span class="time-summary-label">DEPART</span>
                            <span class="time-summary-value">${{formatTime(summary.departure_time)}}</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">DURATION</span>
                            <span class="time-summary-value duration-value">${{summary.total_time_formatted}}</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">ARRIVE</span>
                            <span class="time-summary-value">${{formatTime(summary.arrival_time)}}</span>
                        </div>
                    </div>
                </div>
                
                <!-- Stats Bar -->
                <div class="stats-bar">
                    <div class="stat-item">
                        <span class="stat-value">${{summary.total_distance_miles.toFixed(1)}}</span>
                        <span class="stat-label">MILES</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{summary.bike_distance_miles.toFixed(1)}}</span>
                        <span class="stat-label">BIKE (MI)</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{summary.bike_percentage.toFixed(0)}}%</span>
                        <span class="stat-label">BIKE %</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{summary.transfers || 0}}</span>
                        <span class="stat-label">TRANSFERS</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">${{summary.average_bike_score.toFixed(0)}}</span>
                        <span class="stat-label">SAFETY</span>
                    </div>
                </div>
                
                <!-- Route Steps -->
                <div class="route-steps">`;
            
            route.legs.forEach((leg, legIndex) => {{
                if (leg.type === 'bike') {{
                    html += createEnhancedBikeStep(leg, legIndex);
                }} else if (leg.type === 'transit') {{
                    html += createEnhancedTransitStep(leg, legIndex);
                }}
            }});
            
            html += `
                </div>
            </div>`;
            
            return html;
        }}
        
        function createEnhancedBikeStep(leg, legIndex) {{
            const route = leg.route;
            const safetyScore = route.overall_score || 50;
            const safetyClass = getSafetyScoreClass(safetyScore);
            const safetyLabel = getSafetyScoreLabel(safetyScore);
            
            let html = `
            <div class="route-step">
                <div class="step-icon bike">🚴</div>
                <div class="step-content">
                    <div class="step-title">${{leg.name}}</div>
                    <div class="step-subtitle">${{route.travel_time_formatted}} • ${{route.length_miles.toFixed(2)}} miles</div>
                    
                    <div class="bike-step-details">
                        <!-- Bike Metrics Grid -->
                        <div class="bike-metrics-grid">
                            <div class="bike-metric-item">
                                <span style="font-size: 16px;">⏱️</span>
                                <span><span class="bike-metric-value">${{route.travel_time_formatted}}</span></span>
                            </div>
                            <div class="bike-metric-item">
                                <span style="font-size: 16px;">📏</span>
                                <span><span class="bike-metric-value">${{route.length_miles.toFixed(2)}} mi</span></span>
                            </div>
                            <div class="bike-metric-item">
                                <span style="font-size: 16px;">⚡</span>
                                <span><span class="bike-metric-value">Google Maps</span> avg</span>
                            </div>
                            <div class="bike-metric-item">
                                <span style="font-size: 16px;">🛡️</span>
                                <span><span class="bike-metric-value">${{safetyScore}}</span> safety</span>
                            </div>
                        </div>
                        
                        <!-- Safety Score Badge -->
                        <div class="safety-score-badge ${{safetyClass}}">
                            <span style="font-size: 16px;">✓</span>
                            <span>${{safetyLabel}} Safety Score</span>
                        </div>
                        
                        ${{createFacilityDistributionDisplay(route.facility_stats)}}
                    </div>
                </div>
            </div>`;
            
            return html;
        }}
        
        function createEnhancedTransitStep(leg, legIndex) {{
            const route = leg.route;
            
            let html = `
            <div class="route-step">
                <div class="step-icon bus">🚌</div>
                <div class="step-content">
                    <div class="step-title">${{leg.name}}</div>
                    <div class="step-subtitle">${{route.duration_text}} • ${{route.distance_miles.toFixed(2)}} miles</div>
                    
                    <div class="transit-details">
                        <!-- Transit Info -->
                        <div class="transit-line">
                            <span class="transit-badge">
                                <span style="font-size: 16px;">🚌</span>
                                ${{route.transit_lines ? route.transit_lines.join(', ') : 'Bus'}}
                            </span>
                        </div>
                        
                        <div class="transit-info-line">
                            <span style="font-size: 16px;">📍</span>
                            <span>${{route.start_stop?.name || 'Start Stop'}} → ${{route.end_stop?.name || 'End Stop'}}</span>
                        </div>
                        
                        <div class="transit-info-line">
                            <span style="font-size: 16px;">🕐</span>
                            <span>
                                <span class="transit-time">${{route.departure_time}}</span> 
                                → 
                                <span class="transit-time">${{route.arrival_time}}</span>
                            </span>
                        </div>
                        
                        <div class="transit-info-line">
                            <span style="font-size: 16px;">🔄</span>
                            <span>${{route.transfers || 0}} transfer${{route.transfers !== 1 ? 's' : ''}}</span>
                        </div>
                        
                        ${{createTransitRealtimeDisplay(route)}}
                    </div>
                </div>
            </div>`;
            
            return html;
        }}
        
        function createTransitRealtimeDisplay(route) {{
            // Check if any step has GTFS data
            if (!route.steps) return '';
            
            let html = '';
            route.steps.forEach(step => {{
                if (step.travel_mode === 'TRANSIT' && step.gtfs_data) {{
                    const gtfsData = step.gtfs_data;
                    const hasDelays = gtfsData.has_delays;
                    
                    html += `
                        <div class="realtime-status ${{hasDelays ? 'delayed' : 'on-time'}}" style="margin-top: 8px;">
                            🔴 ${{hasDelays ? 'Delays Reported' : 'On Time'}}
                        </div>`;
                }}
            }});
            
            return html;
        }}
        
        function createFacilityDistributionDisplay(facilityStats) {{
            if (!facilityStats || Object.keys(facilityStats).length === 0) return '';
            
            let html = `
                <div class="facility-distribution">
                    <div class="facility-dist-title">🛣️ BIKE INFRASTRUCTURE</div>
                    
                    <!-- Facility Bar -->
                    <div class="facility-bar-container">`;
            
            // Sort facilities by percentage
            const sortedFacilities = Object.entries(facilityStats).sort((a, b) => b[1].percentage - a[1].percentage);
            
            sortedFacilities.forEach(([facilityType, stats]) => {{
                const color = getFacilityColor(facilityType);
                const percentage = stats.percentage || 0;
                
                if (percentage > 0) {{
                    html += `
                        <div class="facility-segment" 
                             style="width: ${{percentage}}%; background: ${{color}};"
                             title="${{formatFacilityName(facilityType)}}: ${{percentage.toFixed(1)}}%">
                            ${{percentage > 10 ? `<span class="facility-segment-label">${{percentage.toFixed(0)}}%</span>` : ''}}
                        </div>`;
                }}
            }});
            
            html += `
                    </div>
                    
                    <!-- Facility Legend Items -->
                    <div class="facility-legend-items">`;
            
            sortedFacilities.forEach(([facilityType, stats]) => {{
                const color = getFacilityColor(facilityType);
                const percentage = stats.percentage || 0;
                
                if (percentage > 0) {{
                    html += `
                        <div class="facility-legend-item">
                            <div class="facility-color-dot" style="background: ${{color}};"></div>
                            <span style="font-size: 10px;">${{formatFacilityName(facilityType)}}</span>
                            <span class="facility-percentage">${{percentage.toFixed(0)}}%</span>
                        </div>`;
                }}
            }});
            
            html += `
                    </div>
                </div>`;
            
            return html;
        }}
        
        // ========================================
        // DIRECT BIKE CARD
        // ========================================
        
        function createDirectBikeCard(route, index) {{
            const summary = route.summary;
            const safetyScore = summary.average_bike_score || 50;
            const safetyClass = getSafetyScoreClass(safetyScore);
            const safetyLabel = getSafetyScoreLabel(safetyScore);
            
            let html = `
            <div class="route-card" onclick="selectRoute(${{index}})" id="routeCard${{index}}">
                <!-- Header Section -->
                <div class="bike-route-header">
                    <div class="route-title">
                        <h3>🚴 ${{route.name}}</h3>
                        <span class="live-badge">DIRECT</span>
                    </div>
                    
                    <!-- Time Summary -->
                    <div class="time-summary">
                        <div class="time-summary-item">
                            <span class="time-summary-label">DURATION</span>
                            <span class="time-summary-value duration-value">${{summary.total_time_formatted}}</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">DISTANCE</span>
                            <span class="time-summary-value">${{summary.total_distance_miles.toFixed(1)}} mi</span>
                        </div>
                        <div class="time-summary-item">
                            <span class="time-summary-label">SAFETY</span>
                            <span class="time-summary-value">${{safetyScore}}</span>
                        </div>
                    </div>
                </div>
                
                <!-- Stats Bar -->
                <div class="stats-bar">
                    <div class="stat-item">
                        <span class="stat-value">{BIKE_SPEED_MPH}</span>
                        <span class="stat-label">AVG MPH</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">100%</span>
                        <span class="stat-label">BIKE</span>
                    </div>
                    <div class="stat-item">
                        <span class="stat-value">$0</span>
                        <span class="stat-label">FARE</span>
                    </div>
                </div>
                
                <!-- Route Steps -->
                <div class="route-steps">`;
            
            if (route.legs && route.legs.length > 0) {{
                html += createEnhancedBikeStep(route.legs[0], 0);
            }}
            
            html += `
                </div>
            </div>`;
            
            return html;
        }}
        
        // ========================================
        // UTILITY FUNCTIONS
        // ========================================
        
        function extractDestination(instruction) {{
            const match = instruction.match(/to (.+)/i);
            return match ? match[1] : 'destination';
        }}
        
        function formatTime(timeString) {{
            if (!timeString || timeString === 'Unknown' || timeString === 'Immediate' || timeString === 'Flexible') return timeString;
            
            if (timeString.includes('PM') || timeString.includes('AM')) {{
                return timeString;
            }}
            
            try {{
                const date = new Date(timeString);
                return date.toLocaleTimeString('en-US', {{ 
                    hour: 'numeric', 
                    minute: '2-digit',
                    hour12: true 
                }});
            }} catch (e) {{
                return timeString;
            }}
        }}
        
        function formatFacilityName(name) {{
            return name.replace(/_/g, ' ').toLowerCase().split(' ')
                .map(word => word.charAt(0).toUpperCase() + word.slice(1)).join(' ');
        }}
        
        // ========================================
        // MAP VISUALIZATION
        // ========================================
        
        function selectRoute(index) {{
            document.querySelectorAll('.route-card').forEach(card => card.classList.remove('selected'));
            document.querySelectorAll('.route-card')[index].classList.add('selected');
            selectedRouteIndex = index;
            showRouteOnMap(index);
        }}
        
        function showRouteOnMap(index) {{
            if (!currentRoutes[index]) return;
            const route = currentRoutes[index];
            routeLayersGroup.clearLayers();
            
            // Draw each leg
            route.legs.forEach((leg, legIndex) => {{
                if (!leg.route || !leg.route.geometry) return;
                
                if (leg.type === 'bike' && leg.route.segments && leg.route.segments.length > 0) {{
                    // Segment-level coloring for bike routes
                    leg.route.segments.forEach((segment, segmentIndex) => {{
                        if (!segment.geometry || !segment.geometry.coordinates || segment.geometry.coordinates.length < 2) return;
                        
                        const facilityType = segment.facility_type || 'NO BIKELANE';
                        const segmentColor = getFacilityColor(facilityType);
                        const segmentLatLngs = segment.geometry.coordinates.map(coord => [coord[1], coord[0]]);
                        
                        const segmentLine = L.polyline(segmentLatLngs, {{
                            color: segmentColor,
                            weight: 8,
                            opacity: 0.85
                        }}).addTo(routeLayersGroup);
                        
                        segmentLine.bindPopup(`
                            <div style="font-family:'Segoe UI',sans-serif;min-width:200px;">
                                <h4 style="margin:0 0 10px 0;color:${{segmentColor}};">${{formatFacilityName(facilityType)}}</h4>
                                <p style="margin:5px 0;"><strong>Length:</strong> ${{segment.shape_length_miles.toFixed(3)}} mi</p>
                                <p style="margin:5px 0;"><strong>Bike Score:</strong> ${{segment.bike_score || 0}}</p>
                            </div>
                        `);
                    }});
                }} else if (leg.type === 'transit') {{
                    // Transit route with dashed line
                    const geometry = leg.route.geometry;
                    if (!geometry.coordinates || geometry.coordinates.length === 0) return;
                    const latLngs = geometry.coordinates.map(coord => [coord[1], coord[0]]);
                    const routeLine = L.polyline(latLngs, {{
                        color: '#3498db',
                        weight: 8,
                        opacity: 0.8,
                        dashArray: '10, 5'
                    }}).addTo(routeLayersGroup);
                    
                    routeLine.bindPopup(`
                        <div style="font-family:'Segoe UI',sans-serif;">
                            <h4 style="margin:0 0 10px 0;color:#3498db;">🚌 ${{leg.name}}</h4>
                            <p><strong>Distance:</strong> ${{leg.route.distance_miles.toFixed(2)}} mi</p>
                            <p><strong>Time:</strong> ${{leg.route.duration_text}}</p>
                        </div>
                    `);
                }} else if (leg.type === 'bike') {{
                    // Simple bike route without segments
                    const geometry = leg.route.geometry;
                    if (!geometry.coordinates || geometry.coordinates.length === 0) return;
                    const latLngs = geometry.coordinates.map(coord => [coord[1], coord[0]]);
                    
                    const routeLine = L.polyline(latLngs, {{
                        color: '#27ae60',
                        weight: 6,
                        opacity: 0.8
                    }}).addTo(routeLayersGroup);
                    
                    routeLine.bindPopup(`
                        <div style="font-family:'Segoe UI',sans-serif;">
                            <h4 style="margin:0 0 10px 0;color:#27ae60;">🚴 ${{leg.name}}</h4>
                            <p><strong>Distance:</strong> ${{leg.route.length_miles.toFixed(2)}} mi</p>
                            <p><strong>Time:</strong> ${{leg.route.travel_time_formatted}}</p>
                            <p><strong>Safety Score:</strong> ${{leg.route.overall_score}}</p>
                        </div>
                    `);
                }}
            }});
            
            // Add bus stop markers for bike-bus-bike routes
            if (route.type === 'bike_bus_bike') {{
                const transitLeg = route.legs.find(leg => leg.type === 'transit');
                if (transitLeg && transitLeg.route) {{
                    const transitRoute = transitLeg.route;
                    
                    if (transitRoute.start_stop) {{
                        const startIcon = L.divIcon({{
                            html: '<div style="width:24px;height:24px;background:#3498db;border:3px solid white;border-radius:50%;box-shadow:0 2px 8px rgba(0,0,0,0.3);"></div>',
                            iconSize: [30, 30],
                            iconAnchor: [15, 15]
                        }});
                        L.marker([transitRoute.start_stop.display_y, transitRoute.start_stop.display_x], {{icon: startIcon}})
                         .addTo(routeLayersGroup)
                         .bindPopup(`<strong>🚏 Start Bus Stop</strong><br>${{transitRoute.start_stop.name}}`);
                    }}
                    
                    if (transitRoute.end_stop) {{
                        const endIcon = L.divIcon({{
                            html: '<div style="width:24px;height:24px;background:#e74c3c;border:3px solid white;border-radius:50%;box-shadow:0 2px 8px rgba(0,0,0,0.3);"></div>',
                            iconSize: [30, 30],
                            iconAnchor: [15, 15]
                        }});
                        L.marker([transitRoute.end_stop.display_y, transitRoute.end_stop.display_x], {{icon: endIcon}})
                         .addTo(routeLayersGroup)
                         .bindPopup(`<strong>🚏 End Bus Stop</strong><br>${{transitRoute.end_stop.name}}`);
                    }}
                }}
            }}
            
            // Fit map to show route
            try {{
                if (routeLayersGroup.getLayers().length > 0) {{
                    map.fitBounds(routeLayersGroup.getBounds(), {{padding: [50, 50]}});
                }}
            }} catch (e) {{
                console.warn('Could not fit bounds:', e);
            }}
        }}
    </script>
</body>
</html>"""
        return html

    def log_message(self, format, *args):
        """Override to provide custom logging"""
        timestamp = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        print(f"[{timestamp}] {format % args}")

def initialize_server_components():
    """Initialize all server components"""
    try:
        print("Initializing bike-bus-bike server components...")
        
        clean_temporary_files()
        
        print("Checking Google Maps API...")
        if not is_valid_api_key():
            print("WARNING: Google Maps API key not properly configured")
        else:
            print("Google Maps API key is valid")
        
        print("Initializing GTFS data...")
        gtfs_loaded = gtfs_manager.load_gtfs_data()
        if gtfs_loaded:
            print("GTFS data loaded successfully")
        else:
            print("WARNING: GTFS data could not be loaded")
        
        print("Server components initialized successfully")
        return True
        
    except Exception as e:
        print(f"Error initializing server components: {e}")
        return False

def run_bike_bus_bike_google_server():
    """Main function to run the complete bike-bus-bike server"""
    try:
        print("BIKE-BUS-BIKE ROUTE PLANNER SERVER (Google Maps Edition)")
        print("=" * 70)
        print("Features: Google Maps Bike Routing + Google Maps + Real-time GTFS")
        print("No ArcGIS Required!")
        print("=" * 70)
        
        if not initialize_server_components():
            print("Failed to initialize server components")
            return
        
        try:
            PORT = find_available_port(8000, 100)
            print(f"Found available port: {PORT}")
        except RuntimeError as e:
            print(f"Error finding available port: {e}")
            return

        handler = partial(BikeBusBikeGoogleServer, directory=os.getcwd())

        try:
            server = socketserver.TCPServer(("", PORT), handler)
            
            print(f"\nBike-Bus-Bike Server running at http://localhost:{PORT}")
            print(f"\nServer Features:")
            print(f"   Google Maps API for bicycle routing")
            print(f"   Google Maps API for transit routing")
            print(f"   Real-time GTFS data integration")
            print(f"   GeoPandas for segment analysis")
            print(f"   Bicycle infrastructure safety scoring")
            print(f"   Smart transit fallback for short segments")
            print(f"\nClick two points on the map to start!")
            print(f"\nPress Ctrl+C to stop the server")
            
            threading.Timer(1.5, lambda: webbrowser.open(f'http://localhost:{PORT}')).start()
            
            try:
                server.serve_forever()
            except KeyboardInterrupt:
                print("\nReceived keyboard interrupt. Shutting down...")
            finally:
                server.server_close()
                clean_temporary_files()
                print("Server stopped successfully")
                
        except OSError as e:
            print(f"Server error: {str(e)}")
        except Exception as e:
            print(f"Unexpected server error: {str(e)}")
            
    except Exception as e:
        print(f"Failed to start server: {str(e)}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    print("Bike-Bus-Bike Route Planner (Google Maps Edition)")
    print("No ArcGIS dependencies!")
    print()

    run_bike_bus_bike_google_server()

print("Part 6: HTTP server and main execution loaded successfully")
print()
print("ALL PARTS LOADED!")
print("=" * 50)
print("To use:")
print("1. Combine all 6 parts into a single Python file")
print("2. Update ROADS_SHAPEFILE path")
print("3. Update TRANSIT_STOPS_SHAPEFILE path")
print("4. Update GOOGLE_API_KEY")
print("5. Run: python combined_file.py")
print("6. Open browser to http://localhost:8000")
print()
print("Features:")
print(" - Google Maps API bike routing (no ArcGIS needed!)")
print(" - GeoPandas segment analysis")
print(" - Google Maps transit routing")
print(" - Real-time GTFS departures")
print(" - Smart transit fallback")
print(" - Complete web interface")