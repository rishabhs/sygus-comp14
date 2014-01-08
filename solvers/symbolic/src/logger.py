# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# logger.py contains logging service functions

logging = True
    
def IsLogging():
    return logging

def SetLogging(doLog):
	global logging
	logging = doLog