TARGET ?= Top
CC ?= ../HCC.bsv
CC_TEST ?= ../HCCTest.bsv
BUILD_DIR ?= build
TEST_CYCLE_CNT ?= 500000
RQ_TYPE_SEED ?= 3
RQ_BADDR_SEED ?= 79

BSC = bsc \
	+RTS -K100M -RTS \
	-aggressive-conditions \
	-check-assert \
	-steps-max-intervals 100 \
	-bdir $(BUILD_DIR) \
	-info-dir $(BUILD_DIR) \
	-simdir $(BUILD_DIR) \
	-vdir $(BUILD_DIR) \
	-D TEST_CYCLE_CNT=$(TEST_CYCLE_CNT) \
	-D RQ_TYPE_SEED=$(RQ_TYPE_SEED) \
	-D RQ_BADDR_SEED=$(RQ_BADDR_SEED) \
	-p +:../

default: build_all_shared

build_all_shared: $(TARGET).bsv
	touch $(TARGET).bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -D TB_ALL_SHARED=1 -sim -u $(TARGET).bsv
	$(BSC) -D TB_ALL_SHARED=1 -sim -e mkTop -o $(TARGET)

build_pair_shared: $(TARGET).bsv
	touch $(TARGET).bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -D TB_PAIR_SHARED=1 -sim -u $(TARGET).bsv
	$(BSC) -D TB_PAIR_SHARED=1 -sim -e mkTop -o $(TARGET)

build_ex_sh_1: $(TARGET).bsv
	touch $(TARGET).bsv
	touch $(CC_TEST)
	mkdir -p $(BUILD_DIR)
	$(BSC) -D TB_EX_SH=1 -D LG_EX_SH_RATIO=1 -sim -u $(TARGET).bsv
	$(BSC) -D TB_EX_SH=1 -D LG_EX_SH_RATIO=1 -sim -e mkTop -o $(TARGET)

build_ex_sh_2: $(TARGET).bsv
	touch $(TARGET).bsv
	touch $(CC_TEST)
	mkdir -p $(BUILD_DIR)
	$(BSC) -D TB_EX_SH=1 -D LG_EX_SH_RATIO=2 -sim -u $(TARGET).bsv
	$(BSC) -D TB_EX_SH=1 -D LG_EX_SH_RATIO=2 -sim -e mkTop -o $(TARGET)

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(TARGET) $(TARGET).so
