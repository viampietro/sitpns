DIRS=common sitpn

COQINCLUDES=$(foreach d, $(DIRS), -R $(d) hilecop.$(d))

COQCOPTS ?= -w -undeclared-scope
COQC=coqc -q $(COQINCLUDES) $(COQCOPTS)

## Compilation files ##

# General-purpose utilities (in common/)

COMMONFILES=NatMap.v NatSet.v Coqlib.v GlobalTypes.v GlobalFacts.v \
	FstSplit.v InAndNoDup.v ListsPlus.v ListsDep.v \

# Sitpn structures, semantics and token player (in sitpn/simpl/)

SITPNSIMPLFILES=Sitpn.v SitpnSemantics.v SitpnTokenPlayer.v \
	SitpnTactics.v SitpnCoreLemmas.v SitpnWellDefMarking.v \
	SitpnWellDefFired.v SitpnWellDefInterpretation.v SitpnWellDefTime.v \
	SitpnRisingEdgeMarking.v SitpnFallingEdgeWellDef.v SitpnFallingEdgeFired.v \
	SitpnFallingEdgeInterpretation.v SitpnFallingEdgeTime.v \
	SitpnFallingEdgeCorrect.v SitpnRisingEdgeWellDef.v \
	SitpnRisingEdgeTime.v SitpnRisingEdgeInterpretation.v \
	SitpnRisingEdgeCorrect.v SitpnCorrect.v \
	SitpnFallingEdgeInterpretationComplete.v SitpnFallingEdgeFiredComplete.v \
	SitpnFallingEdgeTimeComplete.v SitpnFallingEdgeComplete.v \
	SitpnRisingEdgeMarkingComplete.v SitpnRisingEdgeTimeComplete.v \
	SitpnRisingEdgeInterpretationComplete.v SitpnRisingEdgeComplete.v \
	SitpnComplete.v \

# Sitpn structures, semantics and token player with dependent-types (in sitpn/dp/)

SITPNDPFILES=SitpnTypes.v Sitpn.v SitpnFacts.v SitpnWellDefined.v SitpnSemantics.v \
	InfosTypes.v GenerateInfos.v

# Builds files with prefixes

COMMON=$(foreach f, $(COMMONFILES), common/$f)
SITPNSIMPL=$(foreach f, $(SITPNSIMPLFILES), sitpn/simpl/$f)
SITPNDP=$(foreach f, $(SITPNDPFILES), sitpn/dp/$f)

# All source files

FILES=$(COMMON) $(SITPNSIMPL) $(SITPNDP)

all: proof 

proof: $(FILES:.v=.vo)

common: $(COMMON:.v=.vo)
sitpnsimpl: $(SITPNSIMPL:.v=.vo)
sitpndp: $(SITPNDP:.v=.vo)

%.vo : %.v	
	@echo "COQC $*.v"
	@$(COQC) $*.v

cleancommon:
	rm -f $(patsubst %, %/*.vo, common)
	rm -f $(patsubst %, %/.*.aux, common)
	rm -f $(patsubst %, %/*.glob, common)
	rm -f $(patsubst %, %/*.vok, common)
	rm -f $(patsubst %, %/*.vos, common)
	rm -f $(patsubst %, %/*~, common)

cleansitpn:
	rm -f $(patsubst %, %/*/*.vo, sitpn)
	rm -f $(patsubst %, %/*/.*.aux, sitpn)
	rm -f $(patsubst %, %/*/*.glob, sitpn)
	rm -f $(patsubst %, %/*/*.vok, sitpn)
	rm -f $(patsubst %, %/*/*.vos, sitpn)
	rm -f $(patsubst %, %/*/*~, sitpn)

clean: cleancommon cleansitpn 

