#!/bin/bash

egrep -R "admit|Admitted|Axiom|cheat|give_up|TODO|FIXME" *.v
egrep -R "admit|Admitted|Axiom|cheat|give_up|TODO|FIXME" */*.v
egrep -R "admit|Admitted|Axiom|cheat|give_up|TODO|FIXME" */*/*.v
