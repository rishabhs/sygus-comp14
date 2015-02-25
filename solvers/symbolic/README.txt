Contact: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

Symbolic SyGuS Version 2.0

Requirements: 
- Python 2.7 (I assume python points to python 2.7)
- Z3py
- Pyparsing

Please download and install z3 for your platform from http://z3.codeplex.com. 
This implementation has been tested for version 4.3.0. Let z3 be located at $Z3_ROOT.


Let the root directory of the distribution be $DIR. 
Pyparsing is included in this distribution under $DIR/pyparsing.

To setup:
1. Change current directory to $DIR/pyparsing and run 
   $ python setup.py install
2. Make sure $PYTHONPATH contains $Z3_ROOT/bin

Main sources of the synthesizer are within $DIR/src

Usage: 
python main.py -file /path/to/synthlib_file [-log]

Notes:
1. Version 2.0 does have support for ‘let’ expressions. Any ‘let’ productions are ignored.