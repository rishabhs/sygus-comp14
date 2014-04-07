# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# translator.py contains functions that generate internal data structures
# for the component based synthesis algorithm from the synth lib input


from component import Component, Port, SynthException
from circuit import Circuit, GetValFromType, GetSortFromType
from z3 import And, Bool
import theory
import pprint
import logger

funcDefsMap = {}
synthFunsMap = {}
declaredVar2PortMap = {}
circuitsCache = []


def GenerateCircuit(synthFun, K):
    # K copies of each component
    if len(synthFun) != 5:
        raise SynthException('Wrong synth-fun command')
#   command = synthFun[0]
    funcName = synthFun[1]
    argList = synthFun[2]
    funcRetType = synthFun[3]
    funcGrammar = synthFun[4]

    circuitInputPorts = [
        Port('__CIRCUIT_INP_%s' % argName,
             '__CIRCUIT_%s_%s' % (funcName, argName),
             GetSortFromType(argType))
        for (argName, argType) in argList]

    circuitOutputPort = Port(
        '__CIRCUIT_OUT_%s' %
        funcName, '__CIRCUIT_%s_%s' %
        (funcName, 'Start'), GetSortFromType(funcRetType))

    nonTermTypes = {}
    for nonTermExpansion in funcGrammar:
        nonTermTypes[nonTermExpansion[0]] = nonTermExpansion[1]

    formalArgTypes = {}
    for arg in argList:
        formalArgTypes[arg[0]] = arg[1]

    nonTermTypes.update(formalArgTypes)

    componentBag = []
    for nonTermExpansion in funcGrammar:
        nonTerm = nonTermExpansion[0]
        nonTermType = nonTermExpansion[1]
        productions = nonTermExpansion[2]
        for production in productions:
            if isinstance(production, list):
                if production[0] == 'let':
                    pass
                else:
                    for copyNum in range(0, K):
                        op = theory.GetFunctionFromSymbol(production[0])

                        inputPorts = []
                        for i in range(1, len(production)):
                            inputPorts.append(
                                Port(
                                    '%s_%s_i%d_%d' %
                                    (nonTerm, production[0], i, copyNum),
                                    '__CIRCUIT_%s_%s' %
                                    (funcName, production[i]),
                                    GetSortFromType(
                                        nonTermTypes[
                                            production[i]])))
                        outputPort = Port(
                            '%s_%s_o_%d' %
                            (nonTerm, production[0], copyNum),
                            '__CIRCUIT_%s_%s' %
                            (funcName, nonTerm),
                            GetSortFromType(nonTermType))

                        inputPortVars = [
                            inputPort.var for inputPort in inputPorts]
                        spec = (outputPort.var == op(*inputPortVars))

                        componentBag.append(
                            Component(
                                inputPorts, outputPort, spec, '%s_%s' %
                                (nonTerm, production[0]), production))

            elif isinstance(production, tuple):
                (constType, constVal) = production

                inputPorts = []
                outputPort = Port('%s_c%s_o_%d' % (nonTerm, str(constVal), 0),
                                  '__CIRCUIT_%s_%s' % (funcName, nonTerm),
                                  GetSortFromType(nonTermType))
                spec = (outputPort.var == GetValFromType(constType, constVal))

                componentBag.append(Component(inputPorts, outputPort, spec,
                                              '%s_c%s' % (
                                                  nonTerm, str(constVal)),
                                              production))

            elif isinstance(production, str):
                if not production in [arg[0] for arg in argList]:
                    raise SynthException('Unknown parameter in production')
                inputPorts = [
                    Port(
                        '%s_LIT%s_i_%s' %
                        (nonTerm, production, 0), '__CIRCUIT_%s_%s' %
                        (funcName, production), GetSortFromType(
                            formalArgTypes[production]))]
                outputPort = Port('%s_LIT%s_o_%s' % (nonTerm, production, 0),
                                  '__CIRCUIT_%s_%s' % (funcName, nonTerm),
                                  GetSortFromType(nonTermType))
                spec = (outputPort.var == inputPorts[0].var)

                componentBag.append(Component(inputPorts, outputPort, spec,
                                              '%s_LIT%s' % (
                                                  nonTerm, production),
                                              production))

            else:
                raise SynthException('Unknown kind of production')

    return Circuit(
        funcName, componentBag, circuitInputPorts, circuitOutputPort)


def GenerateFunctionConstraints(spec, localVarConstraintsMap):

    if not isinstance(spec, list):
        if isinstance(spec, tuple):
            (typ, raw_val) = spec
            return GetValFromType(typ, raw_val)
        raise SynthException('Improper function call %s'%spec)

    if logger.IsLogging():
        print spec
    opSym = spec[0]
    argConstraints = []

    for arg in spec[1:]:
        if arg in localVarConstraintsMap.keys():
            argConstraints.append(localVarConstraintsMap[arg])
        elif isinstance(arg, tuple):
            (typ, raw_val) = arg
            argConstraints.append(GetValFromType(typ, raw_val))
        elif arg in funcDefsMap.keys():
            funcDef = funcDefsMap[arg]
            funcFormalArgsList = funcDef[2]
            funcDefExpr = funcDef[4]

            if funcFormalArgsList:
                raise SynthException('Cannot call constant function' +
                ' with arguments')
            argConstraints.append(GenerateFunctionConstraints(
                funcDefExpr, localVarConstraintsMap))

        else:
            funcConstraint = GenerateFunctionConstraints(
                arg, localVarConstraintsMap)
            argConstraints.append(funcConstraint)

    if opSym in funcDefsMap:
        funcDef = funcDefsMap[opSym]
        funcFormalArgsList = funcDef[2]
        funcDefExpr = funcDef[4]

        newLocalVarConstraintsMap = {}
        for ii in range(len(funcFormalArgsList)):
            formalArg = funcFormalArgsList[ii]
            formalArgName = formalArg[0]
            newLocalVarConstraintsMap[formalArgName] = argConstraints[ii]
        return GenerateFunctionConstraints(
            funcDefExpr, newLocalVarConstraintsMap)

    elif opSym in synthFunsMap:
        raise SynthException(
            'Synth function call cannot be within a defined function')
    else:
        op = theory.GetFunctionFromSymbol(opSym)
        return op(*argConstraints)


def GenerateAll(spec, K, localVarConstraintsMap):
    if logger.IsLogging():
        print spec
    if not isinstance(spec, list):
        raise SynthException('Improper function call %r' % spec)

    opSym = spec[0]
    argConstraints = []
    specConnList = []
    circuitList = []
    for arg in spec[1:]:
        if arg in localVarConstraintsMap.keys():
            argConstraints.append(localVarConstraintsMap[arg])
        elif arg in declaredVar2PortMap.keys():
            argConstraints.append(declaredVar2PortMap[arg].var)
        elif isinstance(arg, tuple):
            (typ, raw_val) = arg
            argConstraints.append(GetValFromType(typ, raw_val))
        # specifically for constant functions
        elif arg in funcDefsMap.keys():
            funcDef = funcDefsMap[arg]
            funcFormalArgsList = funcDef[2]
            funcDefExpr = funcDef[4]

            if funcFormalArgsList:
                raise SynthException('Cannot call constant function' +
                ' with arguments')
            (typ, raw_val) = funcDefExpr
            argConstraints.append(GetValFromType(typ, raw_val))
        else:
            (funcConstraint, specConns, circuits) = GenerateAll(arg, K,
                    localVarConstraintsMap)
            argConstraints.append(funcConstraint)
            specConnList.extend(specConns)
            circuitList.extend(circuits)

    if opSym in funcDefsMap:
        funcDef = funcDefsMap[opSym]
        funcFormalArgsList = funcDef[2]
        funcDefExpr = funcDef[4]

        newLocalVarConstraintsMap = {}
        for ii in range(len(funcFormalArgsList)):
            formalArg = funcFormalArgsList[ii]
            formalArgName = formalArg[0]
            newLocalVarConstraintsMap[formalArgName] = argConstraints[ii]

        (funcDefExprConstraint, specConns, circuits) = GenerateAll(
            funcDefExpr, K,
            newLocalVarConstraintsMap)
        specConnList.extend(specConns)
        circuitList.extend(circuits)
        return (funcDefExprConstraint, specConnList, circuitList)

    elif opSym in synthFunsMap:
        if not localVarConstraintsMap:
            if spec in [circuitExpr for (circuitExpr, _) in circuitsCache]:
                circuit = next(
                        circ for (expr, circ) in circuitsCache if expr == spec)
                return (circuit.outputPort.var, [], [])

        circuit = GenerateCircuit(synthFunsMap[opSym], K)
        if not localVarConstraintsMap:
            circuitsCache.append((spec, circuit))
        circuitList.append(circuit)
        if len(circuit.inputPorts) != len(argConstraints):
            raise SynthException('Improper function call at %r' % spec)
        for ii in range(len(circuit.inputPorts)):
            specConnList.append(circuit.inputPorts[ii].var ==
                    argConstraints[ii])

        return (circuit.outputPort.var, specConnList, circuitList)

    else:
        op = theory.GetFunctionFromSymbol(opSym)
        return (op(*argConstraints), specConnList, circuitList)


def JoinConstraints(specificationConstraints):
    if len(specificationConstraints) == 1:
        return specificationConstraints[0]
    else:
        return ['and', specificationConstraints[0],
                JoinConstraints(specificationConstraints[1:])]


def ReadQuery(synthesisQuery, K):
    global funcDefsMap
    global synthFunsMap
    global declaredVar2PortMap
    global circuitsCache
    funcDefsMap = {}
    synthFunsMap = {}
    declaredVar2PortMap = {}
    circuitsCache = []
    spec = Bool(True)
    specInputPorts = []
    specConnList = []
    circuits = []
    specificationConstraints = []
    for command in synthesisQuery:
        commandName = command[0]
        if commandName == 'define-fun':
            funcDefsMap[command[1]] = command
        elif commandName == 'synth-fun':
            synthFunsMap[command[1]] = command
        elif commandName == 'declare-var':
            varName = command[1]
            varType = command[2]
            declaredVar2PortMap[
                command[1]] = Port(
                '__DECVAR_%s' %
                (varName),
                '__SPEC_%s' %
                (varName),
                GetSortFromType(varType))
        elif commandName == 'constraint':
            specificationConstraints.append(command[1])
        elif commandName == 'check-synth':
            specInputPorts = [
                port for (_, port) in declaredVar2PortMap.iteritems()]
            (spec, specConnList, circuits) = GenerateAll(
                JoinConstraints(specificationConstraints), K, {})
        else:
            pass
    return (spec, specInputPorts, And(specConnList), circuits)
