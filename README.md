# activate env
cd ~/CLA
source venv_cocotb181/bin/activate

# run gp4 tests
MAKEFLAGS=-j4 pytest --exitfirst --capture=no testbench.py -k test_runCocotbTestsGp4

# run cla tests
MAKEFLAGS=-j4 pytest --exitfirst --capture=no testbench.py -k test_runCocotbTestsCla

python --version      # 3.10.x
verilator --version   # 5.042 or similar
python -m pip show cocotb
