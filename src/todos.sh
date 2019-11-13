#!/bin/bash

egrep -R "TODO|FIXME" *.v
egrep -R "TODO|FIXME" */*.v
egrep -R "TODO|FIXME" */*/*.v
