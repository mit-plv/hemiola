TARGET ?= Top
BUILD_DIR ?= build
TEST_CYCLE_CNT ?= 200000
RQ_TYPE_SEED ?= 3
RQ_BADDR_SEED ?= 79

BSC ?= bsc \
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

all: $(TARGET).bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -sim -u $(TARGET).bsv
	$(BSC) -sim -e mkTop -o $(TARGET)

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(TARGET) $(TARGET).so
