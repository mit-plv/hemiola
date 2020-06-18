CONNECTALDIR?=../connectal
S2H_INTERFACES = HostRequest:Host.request
H2S_INTERFACES = Host:HostIndication

BSVFILES= Host.bsv
CPPFILES= SoftwareHost.cpp Tests.cpp

CONNECTALFLAGS+= --mainclockperiod=12
CONNECTALFLAGS+= --bscflags="-aggressive-conditions +RTS -K100M -RTS -steps-max-intervals 10000000"
CONNECTALFLAGS+= --bsvpath=".."

include $(CONNECTALDIR)/Makefile.connectal

