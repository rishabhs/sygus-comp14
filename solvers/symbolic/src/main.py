# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# main.py is the main file that the user should run

import sys
import time
from translator import ReadQuery
from synth import Synthesize
import logger
import sexp
import pprint

benchmarkFileName = ""
doLog = False


def parseArguments(args):
    if not args:
        return
    option = args[0]
    if option == "-file":
        global benchmarkFileName
        benchmarkFileName = args[1]
        parseArguments(args[2:])
    elif option == "-log":
        global doLog
        doLog = True
        parseArguments(args[1:])
    else:
        raise Exception('Unknown command line option.')


def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


if __name__ == '__main__':
    if (len(sys.argv) < 2):
        print 'Usage: %s -file <Synth File> \n' % sys.argv[0]
        sys.exit(1)
    AppStartTime = time.clock()

    parseArguments(sys.argv[1:])

    try:
        benchmarkFile = open(benchmarkFileName)
    except:
        print 'No file found. Usage: %s -file <Synth File> \n' % sys.argv[0]
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]

    logger.SetLogging(doLog)

    if logger.IsLogging():
        pprint.pprint(bmExpr)

    numCopies = 1
    while True:
        (spec, specInputPorts,
         specConn, circuits) = ReadQuery(bmExpr, numCopies)
        if logger.IsLogging():
            print 'Spec:%r' % spec
            print 'SpecConn:%r' % specConn
            print 'Number of Circuits:%i' % len(circuits)
            print 'Circuits:%r' % circuits

        if Synthesize(spec, specInputPorts, specConn, circuits):
            break
        else:
            numCopies += 1

    AppFinishTime = time.clock()
    AppTotalTime = AppFinishTime - AppStartTime
    if logger.IsLogging():
        print 'Overall synthesis took %f seconds.' % (AppTotalTime)
