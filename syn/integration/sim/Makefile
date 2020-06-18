TARGET ?= Top
BUILD_DIR ?= build
BSC ?= bsc \
	-aggressive-conditions \
	-bdir $(BUILD_DIR) \
	-info-dir $(BUILD_DIR) \
	-simdir $(BUILD_DIR) \
	-vdir $(BUILD_DIR) \
	-p +:../

all: $(TARGET).bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -sim -u $(TARGET).bsv
	$(BSC) -sim -e mkTop -o $(TARGET)

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(TARGET) $(TARGET).so
