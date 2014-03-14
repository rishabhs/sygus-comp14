# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# synth.py contains the core CEGIS loop
# refer to http://www.eecs.berkeley.edu/~sseshia/pubdir/fmcad13-sygus.pdf
# for details

import z3printer
from z3 import Int, And, Bool, substitute, Not, Solver, unsat
import logger
from component import SynthException


def setup():
    z3printer._Formatter.max_depth = 10000
    z3printer._Formatter.max_args = 100000
    z3printer._Formatter.max_visited = 1000000
    z3printer._PP.max_width = 200
    z3printer._PP.bounded = False
    z3printer._PP.max_lines = 1000000


def GenerateCircuitSimilarityConstraints(circuits):
    constraints = [Bool(True)]

    numCircuits = len(circuits)

    for i in range(numCircuits):
        for j in range(i+1, numCircuits):
            circuitX = circuits[i]
            circuitY = circuits[j]

            if circuitX.funcName == circuitY.funcName:
                numComponentsX = len(circuitX.components)
                numComponentsY = len(circuitY.components)

                if numComponentsX != numComponentsY:
                    raise SynthException('circuits for same function must' +
                                         'have same number of components')

                for comp_no in range(numComponentsX):
                    compX = circuitX.components[comp_no]
                    compY = circuitY.components[comp_no]

                    numInputPortsX = len(compX.inputPorts)
                    numInputPortsY = len(compY.inputPorts)

                    if numInputPortsY != numInputPortsX:
                        raise SynthException('similar components must have' +
                                             'same number of input ports')

                    for port_no in range(numInputPortsX):
                        constraints.append(
                            Int(circuitX.PN2LNMap[
                                compX.inputPorts[port_no].name]) ==
                            Int(circuitY.PN2LNMap[
                                compY.inputPorts[port_no].name]))
                    constraints.append(
                        Int(circuitX.PN2LNMap[compX.outputPort.name]) ==
                        Int(circuitY.PN2LNMap[compY.outputPort.name]))

    return And(constraints)


def GenerateVerificationConstraint(spec, specConn, circuits,
                                   psiConn, circuitModel):
    constraints = [Bool(True)]

    substList = []
    for circuit in circuits:
        substList.extend([(Int(labelName),
                           circuitModel.eval(Int(labelName), True))
                          for (_, labelName) in circuit.labels.iteritems()])

    constraints.append(substitute(psiConn, substList))
    constraints.append(specConn)
    constraints.append(Not(spec))
    return And(constraints)


def GetExampleFromInputModel(inputModel, specInputPorts):
    return {specInputPort: inputModel.eval(specInputPort.var)
            for specInputPort in specInputPorts}


def GenerateConstraintForExample(spec, specConn, circuits,
                                 psiConn, newExample, iteration):
    substList = []

    for circuit in circuits:
        substList.append(
            (circuit.outputPort.var,
             circuit.outputPort.GenVarCopyForIteration(iteration)))
        substList.extend(
            [(circuitInputPort.var,
              circuitInputPort.GenVarCopyForIteration(iteration))
             for circuitInputPort in circuit.inputPorts])

        for comp in circuit.components:
            substList.append(
                (comp.outputPort.var,
                 comp.outputPort.GenVarCopyForIteration(iteration)))
            substList.extend([(inputPort.var,
                               inputPort.GenVarCopyForIteration(iteration))
                              for inputPort in comp.inputPorts])

    substList.extend((port.var, val) for (port, val) in newExample.iteritems())

    constraints = [Bool(True)]

    constraints.append(substitute(psiConn, substList))
    constraints.append(substitute(specConn, substList))
    constraints.append(substitute(spec, substList))

    return And(constraints)


def Synthesize(spec, specInputPorts, specConn, circuits):
    wellFormedConstraints = [Bool(True)]

    for circuit in circuits:
        wellFormedConstraints.append(
            circuit.GenerateWellFormednessConstraints())

    wellFormedConstraints.append(
        GenerateCircuitSimilarityConstraints(circuits))

    psiWfp = And(wellFormedConstraints)

    psiConn = And([circuit.GenerateConnectionConstraints()
                   for circuit in circuits])
    #if logger.IsLogging(): print psiConn

    examples = []

    iterCounter = 0
    synthSolver = Solver()
    verifSolver = Solver()

    synthSolver.assert_exprs(psiWfp)
    synthSolver.assert_exprs(GenerateConstraintForExample(
        spec, specConn, circuits,
        psiConn, {}, iterCounter))

    while True:
        iterCounter += 1
        if logger.IsLogging():
            print 'Attempting Synthesis...'

        if synthSolver.check() == unsat:
            if logger.IsLogging():
                print 'Synth Failed!'
            return False

        model = synthSolver.model()
        if logger.IsLogging():
            print 'Synthesized program:\n'

        if logger.IsLogging():
            for circuit in circuits:
                print circuit.funcName
                print circuit.LValToProg(model)
                print '\n'

        verifConstraint = GenerateVerificationConstraint(
            spec, specConn,
            circuits, psiConn, model)

        verifSolver.push()
        verifSolver.assert_exprs(verifConstraint)

        if logger.IsLogging():
            print 'Attempting Verification...'
        #if logger.IsLogging(): print verifConstraint
        #raw_input("waiting for keypress")
        if (verifSolver.check() == unsat):
            if logger.IsLogging():
                print 'Verification succeeded!\n'
            verifSolver.pop()
            if logger.IsLogging():
                print 'Took %d iterations to complete synthesis' % iterCounter
            if logger.IsLogging():
                print 'Final Circuits:\n'
            printedCircuits = []
            for circuit in circuits:
                if not circuit.funcName in printedCircuits:
                    print circuit.GenerateCircuitExpression(model)
                printedCircuits.append(circuit.funcName)
            return True

        if logger.IsLogging():
            print 'Verification Failed!\n'
        newExample = GetExampleFromInputModel(verifSolver.model(),
                                              specInputPorts)
        verifSolver.pop()
        examples.append(newExample)

        synthConstraintForExample = GenerateConstraintForExample(
            spec, specConn, circuits, psiConn,
            newExample, iterCounter)

        synthSolver.assert_exprs(synthConstraintForExample)

        if logger.IsLogging():
            print 'Added Example %d:' % iterCounter
        if logger.IsLogging():
            print newExample
