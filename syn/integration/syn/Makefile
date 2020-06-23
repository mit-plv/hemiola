CONNECTALDIR?=../connectal
S2H_INTERFACES = HostRequest:Host.request
H2S_INTERFACES = Host:HostIndication

BSVFILES= Host.bsv
CPPFILES= SoftwareHost.cpp

RQ_TYPE_SEED ?= 3
RQ_BADDR_SEED ?= 79

CONNECTALFLAGS+= --mainclockperiod=16
CONNECTALFLAGS+= --bscflags="-aggressive-conditions +RTS -K100M -RTS -steps-max-intervals 10000000"
CONNECTALFLAGS+= --bscflags="-D RQ_TYPE_SEED=$(RQ_TYPE_SEED)"
CONNECTALFLAGS+= --bscflags="-D RQ_BADDR_SEED=$(RQ_BADDR_SEED)"
CONNECTALFLAGS+= --bsvpath=".."

include $(CONNECTALDIR)/Makefile.connectal

