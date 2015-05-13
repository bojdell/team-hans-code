################################################################################
# Automatically-generated file. Do not edit!
################################################################################

SHELL = cmd.exe

CG_TOOL_ROOT := C:/CCStudio_v6.0/ccsv6/tools/compiler/c6000_7.4.8

ORDERED_OBJS += \
$(GEN_CMDS__FLAG) \
"./user_xy.obj" \
"./user_final_project_1.obj" \
"./pru.obj" \
"./final_project_1cfg_c.obj" \
"./final_project_1cfg.obj" \
"./MatrixMath.obj" \
"./Ladar.obj" \
"./LCDprintf.obj" \
"./ColorVision.obj" \
"./ColorLCD.obj" \
"./COECSL_mcbsp.obj" \
"./COECSL_edma3.obj" \
"C:/_team_hans/repo/c67xmathlib_2_01_00_00/lib/c674xfastMath.lib" \
"C:/_team_hans/repo/bsl/lib/evmomapl138_bsl.lib" \
"C:/_team_hans/repo/final_project_1/lnk.cmd" \
-l"libc.a" \

-include ../makefile.init

RM := DEL /F
RMDIR := RMDIR /S/Q

# All of the sources participating in the build are defined here
-include sources.mk
-include subdir_vars.mk
-include subdir_rules.mk
-include objects.mk

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(S_DEPS)),)
-include $(S_DEPS)
endif
ifneq ($(strip $(S_UPPER_DEPS)),)
-include $(S_UPPER_DEPS)
endif
ifneq ($(strip $(S62_DEPS)),)
-include $(S62_DEPS)
endif
ifneq ($(strip $(C64_DEPS)),)
-include $(C64_DEPS)
endif
ifneq ($(strip $(ASM_DEPS)),)
-include $(ASM_DEPS)
endif
ifneq ($(strip $(CC_DEPS)),)
-include $(CC_DEPS)
endif
ifneq ($(strip $(S55_DEPS)),)
-include $(S55_DEPS)
endif
ifneq ($(strip $(C67_DEPS)),)
-include $(C67_DEPS)
endif
ifneq ($(strip $(C??_DEPS)),)
-include $(C??_DEPS)
endif
ifneq ($(strip $(CLA_DEPS)),)
-include $(CLA_DEPS)
endif
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
ifneq ($(strip $(S??_DEPS)),)
-include $(S??_DEPS)
endif
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
ifneq ($(strip $(C62_DEPS)),)
-include $(C62_DEPS)
endif
ifneq ($(strip $(CXX_DEPS)),)
-include $(CXX_DEPS)
endif
ifneq ($(strip $(C++_DEPS)),)
-include $(C++_DEPS)
endif
ifneq ($(strip $(ASM_UPPER_DEPS)),)
-include $(ASM_UPPER_DEPS)
endif
ifneq ($(strip $(K_DEPS)),)
-include $(K_DEPS)
endif
ifneq ($(strip $(C43_DEPS)),)
-include $(C43_DEPS)
endif
ifneq ($(strip $(S67_DEPS)),)
-include $(S67_DEPS)
endif
ifneq ($(strip $(SA_DEPS)),)
-include $(SA_DEPS)
endif
ifneq ($(strip $(S43_DEPS)),)
-include $(S43_DEPS)
endif
ifneq ($(strip $(OPT_DEPS)),)
-include $(OPT_DEPS)
endif
ifneq ($(strip $(S64_DEPS)),)
-include $(S64_DEPS)
endif
ifneq ($(strip $(C_UPPER_DEPS)),)
-include $(C_UPPER_DEPS)
endif
ifneq ($(strip $(C55_DEPS)),)
-include $(C55_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables 
EXE_OUTPUTS += \
final_project_1.out \

EXE_OUTPUTS__QUOTED += \
"final_project_1.out" \


# All Target
all: final_project_1.out

# Tool invocations
final_project_1.out: $(OBJS) $(CMD_SRCS) $(LIB_SRCS) $(GEN_CMDS)
	@echo 'Building target: $@'
	@echo 'Invoking: C6000 Linker'
	"C:/CCStudio_v6.0/ccsv6/tools/compiler/c6000_7.4.8/bin/cl6x" -mv6740 --abi=coffabi -O3 -g --define=RUNNING_ON_OMAPL138 --define=_DEBUG --display_error_number --diag_warning=225 -z --stack_size=0xc00 -m"final_project_1.map" -i"C:/CCStudio_v6.0/ccsv6/tools/compiler/c6000_7.4.8/lib" -i"C:/CCStudio_v6.0/ccsv6/tools/compiler/c6000_7.4.8/include" -i"C:/CCStudio_v6.0/bios_5_42_01_09/packages/ti/rtdx/lib/c6000" -i"C:/CCStudio_v6.0/bios_5_42_01_09/packages/ti/bios/lib" --reread_libs --warn_sections --xml_link_info="final_project_1_linkInfo.xml" --rom_model -o "final_project_1.out" $(ORDERED_OBJS)
	@echo 'Finished building target: $@'
	@echo ' '
	@$(MAKE) --no-print-directory post-build

# Other Targets
clean:
	-$(RM) $(GEN_HDRS__QUOTED)$(GEN_MISC_FILES__QUOTED)$(EXE_OUTPUTS__QUOTED)$(GEN_FILES__QUOTED)$(GEN_CMDS__QUOTED)
	-$(RM) "COECSL_edma3.pp" "COECSL_mcbsp.pp" "ColorLCD.pp" "ColorVision.pp" "LCDprintf.pp" "Ladar.pp" "MatrixMath.pp" "final_project_1cfg_c.pp" "pru.pp" "user_final_project_1.pp" "user_xy.pp" 
	-$(RM) "final_project_1cfg.pp" 
	-$(RM) "COECSL_edma3.obj" "COECSL_mcbsp.obj" "ColorLCD.obj" "ColorVision.obj" "LCDprintf.obj" "Ladar.obj" "MatrixMath.obj" "final_project_1cfg.obj" "final_project_1cfg_c.obj" "pru.obj" "user_final_project_1.obj" "user_xy.obj" 
	-@echo 'Finished clean'
	-@echo ' '

post-build:
	-"C:/_team_hans/repo/final_project_1/final_project_1Project/../postBuildStep_Debug.bat" PROJECT_ROOT C:/_team_hans/repo/final_project_1/final_project_1Project !
	-@echo ' '

.PHONY: all clean dependents
.SECONDARY: post-build

-include ../makefile.targets

