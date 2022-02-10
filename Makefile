# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# Signifies our desired python version
# Makefile macros (or variables) are defined a little bit differently than traditional bash, keep 
# in mind that in the Makefile there's top-level Makefile-only syntax, and everything else is bash 
# script syntax.
PYTHON = python
PIP = ${PYTHON} -m pip

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

.DEFAULT_GOAL = help

# The @ makes sure that the command itself isn't echoed in the terminal
help:
	@echo "+---------------------------------------------------+"
	@echo "|         OS         |  Hardware  |  Setup Command  |"
	@echo "+---------------------------------------------------+"
	@echo "|   Windows/Linux    |   - GPU    |   'make setup'  |"
	@echo "|   Windows/Linux    |   + GPU    |   'make setup'  |"
	@echo "|    Apple macOS     |    + M1    |   'make setup'  |"
	@echo "|    Apple macOS     |    - M1    |   'make setup'  |"
	@echo "+---------------------------------------------------+"

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

setup:
	${PIP} install -r ./requirements.txt
cp:
	${PYTHON} src/cp.py

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# .PHONY defines parts of the makefile that are not dependant on any specific file
# This is most often used to store functions
.PHONY: help
.PHONY: setup
.PHONY: cp
