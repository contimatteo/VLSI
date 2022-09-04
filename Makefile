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
	@echo "+-------------------------------------------------+"
	@echo "|    OS    |    Hardware    |    Setup Command    |"
	@echo "+-------------------------------------------------+"
	@echo "|    //    |       CPU       |  'make setup.CPU'  |"
	@echo "|    //    |    Apple M1     |  'make setup.M1'   |"
	@echo "+-------------------------------------------------+"

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

setup.CPU:
	pip install -r tools/requirements/CPU.txt
setup.M1:
	pip install -r tools/requirements/M1.txt

CP.run.all:
	sh scripts/CP.sh
SAT.run.all:
	sh scripts/SAT.sh
SMT.run.all:
	sh scripts/SMT.sh
ILP.run.all:
	sh scripts/ILP.sh

test:
	python -m pytest -rP tests

clean:
	rm -rf __pycache__

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# .PHONY defines parts of the makefile that are not dependant on any specific file
# This is most often used to store functions
.PHONY: help
.PHONY: setup.CPU
.PHONY: setup.M1
.PHONY: CP.run.all
.PHONY: SAT.run.all
.PHONY: SMT.run.all
.PHONY: ILP.run.all
.PHONY: test
.PHONY: clean
