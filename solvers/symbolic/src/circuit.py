# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# circuit.py contains the definitions for a (to-be-synthezied)
# circuit (or function expression) and realted functions

import sys
from z3 import (Int, And, Bool, Implies,
                IntSort, BoolSort, BitVecSort, IntVal, BoolVal, BitVecVal,
                is_bv_sort)
from component import SynthException

if __name__ == "__main__":
    print 'This module is only intended to be used as a library!\n'
    sys.exit(1)


def GetSortFromType(typ):
    if typ == 'Int':
        return IntSort()
    elif typ == 'Bool':
        return BoolSort()
    elif isinstance(typ, list):
        if (len(typ) != 2 or typ[0] != 'BitVec'):
            raise SynthException('Unknown Type %r' % (typ))
        else:
            intName, size = typ[1]
            return BitVecSort(size)
    else:
        raise SynthException('Unknown Type %r' % (typ))

def GetStringFromType(typ):
    srt = GetSortFromType(typ)
    if srt == IntSort():
        return 'Int'
    elif srt == BoolSort():
        return 'Bool'
    elif is_bv_sort(srt):
        sz = srt.size()
        return '(BitVec ' + str(sz) + ')'
    else:
        raise SynthException('Unknonw sort for string conversion.')

def GetValFromType(typ, raw_val):
    srt = GetSortFromType(typ)
    if srt == IntSort():
        return IntVal(raw_val)
    elif srt == BoolSort():
        return BoolVal(raw_val)
    elif is_bv_sort(srt):
        sz = srt.size()
        return BitVecVal(raw_val, sz)
    else:
        raise SynthException('Unknown sort')


class Circuit:
    numCircuits = 0

    def __init__(self, funcName, components, inputPorts, outputPort, synthFun):
        self.funcName = funcName
        self.components = components
        self.inputPorts = inputPorts
        self.outputPort = outputPort
        self.synthFun = synthFun
        self.id = Circuit.numCircuits
        Circuit.numCircuits += 1
        self.GenerateLabels()

    def __repr__(self):
        retVal = '<Circuit for %s_%s:\n\t' % (self.funcName, str(self.id))
        for inputPort in self.inputPorts:
            retVal += '%s,' % (inputPort.name)
        retVal += '--> %s\n' % (self.outputPort.name)
        for component in self.components:
            retVal += '\n\t%r' % component
        retVal += '>'
        return retVal

    def GenerateLabels(self):
        numLabels = 0
        labels = {}
        compPortNameToLabelNameMap = {}
        labelNameToCompPortMap = {}

        for comp in self.components:
            inputLabels = []
            for i in range(len(comp.inputPorts)):
                labelName = 'L_%s_i_%02d' % (comp.GetIndexedName(), i)
                labels[numLabels] = labelName
                numLabels += 1
                compPortNameToLabelNameMap[comp.inputPorts[i].name] = labelName
                labelNameToCompPortMap[labelName] = comp.inputPorts[i]
                inputLabels.append(labelName)
            comp.SetInputLabels(inputLabels)

        for comp in self.components:
            labelName = 'L_%s_o' % comp.GetIndexedName()
            labels[numLabels] = labelName
            numLabels += 1
            compPortNameToLabelNameMap[comp.outputPort.name] = labelName
            labelNameToCompPortMap[labelName] = comp.outputPort
            comp.SetOutputLabel(labelName)

        self.PN2LNMap = compPortNameToLabelNameMap
        self.LN2PMap = labelNameToCompPortMap
        self.labels = labels

    def GenerateLabelRangeConstraints(self):
        constraints = [Bool(True)]
        numInputPorts = len(self.inputPorts)
        numComponents = len(self.components)

        inputLabelLo = 0
        inputLabelHi = numInputPorts + numComponents
        outputLabelLo = numInputPorts
        outputLabelHi = numInputPorts + numComponents

        for comp in self.components:
            for inputPort in comp.inputPorts:
                constraints.append(Int(self.PN2LNMap[inputPort.name])
                                   >= inputLabelLo)
                constraints.append(Int(self.PN2LNMap[inputPort.name])
                                   < inputLabelHi)

            constraints.append(Int(self.PN2LNMap[comp.outputPort.name])
                               >= outputLabelLo)
            constraints.append(Int(self.PN2LNMap[comp.outputPort.name])
                               < outputLabelHi)

        return And(constraints)

    def GenerateDistinctOutputLabelConstraints(self):
        constraints = [Bool(True)]

        for i in range(len(self.components)):
            for j in range(i+1, len(self.components)):
                dist_ij = (Int(self.PN2LNMap[
                               self.components[i].outputPort.name]) !=
                           Int(self.PN2LNMap[
                               self.components[j].outputPort.name]))
                constraints.append(dist_ij)

        return And(constraints)

    def GenerateAcycConstraints(self):
        constraints = [Bool(True)]

        for comp in self.components:
            for inputPort in comp.inputPorts:
                constraints.append(Int(self.PN2LNMap[inputPort.name]) <
                                   Int(self.PN2LNMap[comp.outputPort.name]))

        return And(constraints)

    def GenerateWellFormednessConstraints(self):
        psiRange = self.GenerateLabelRangeConstraints()
        psiDiffLoc = self.GenerateDistinctOutputLabelConstraints()
        psiAcyc = self.GenerateAcycConstraints()

        return And(psiRange, psiDiffLoc, psiAcyc)

    def GenerateConnectionConstraints(self):
        constraints = [Bool(True)]
        numInputPorts = len(self.inputPorts)
        numComponents = len(self.components)

        for i in range(numInputPorts):
            for comp in self.components:
                for inputPort in comp.inputPorts:
                    if inputPort.breed == self.inputPorts[i].breed:
                        antecedent = (Int(self.PN2LNMap[inputPort.name]) == i)
                        consequent = (inputPort.var == self.inputPorts[i].var)
                        constraints.append(Implies(antecedent, consequent))
                    else:
                        constraints.append(Int(self.PN2LNMap[inputPort.name])
                                           != i)

        numLabels = len(self.labels)

        for i in range(numLabels):
            for j in range(i+1, numLabels):
                labelX = self.labels[i]
                labelY = self.labels[j]

                portX = self.LN2PMap[labelX]
                portY = self.LN2PMap[labelY]

                if portX.breed == portY.breed:
                    antecedent = Int(labelX) == Int(labelY)
                    consequent = (portX.var == portY.var)
                    constraints.append(Implies(antecedent, consequent))
                else:
                    constraints.append(Int(labelX) != Int(labelY))

        for comp in self.components:
            if comp.outputPort.breed == self.outputPort.breed:
                antecedent = (Int(self.PN2LNMap[comp.outputPort.name]) ==
                              numInputPorts + numComponents - 1)
                consequent = (self.outputPort.var == comp.outputPort.var)
                constraints.append(Implies(antecedent, consequent))
            else:
                constraints.append(Int(self.PN2LNMap[comp.outputPort.name]) !=
                                   numInputPorts + numComponents - 1)

        constraints.extend([comp.spec for comp in self.components])

        return And(constraints)

    def GetLModel(self, model):
        return {labelName: int(model.eval(Int(labelName), True).__repr__())
                for (_, labelName) in self.labels.iteritems()}

    # Helper functions for LValToProg
    def ConstructProgramListing(self, LModel):
        ProgList = [None] * (len(self.components))

        for comp in self.components:
            Pos = LModel[comp.outputLabel] - len(self.inputPorts)
            ProgList[Pos] = comp
            comp.SetPosition(Pos)

        return ProgList

    def RefineProgList(self, ProgList, LModel):
        # The last element in the proglist is the output
        #WorkList = [ProgList[len(ProgList) - 1]]

        WorkList = [ProgList[len(self.components) - 1]]
        RefinedProgList = []
        VisitedSet = set()
        VisitedSet.add(WorkList[0])
        while len(WorkList) > 0:
            WorkList = list(reversed(sorted(WorkList,
                                            key=lambda Comp: Comp.pos)))
            CurComp = WorkList.pop(0)
            CompArgs = []
            # Handle constants differently

            for InputLabel in CurComp.inputLabels:
                if (LModel[InputLabel] < len(self.inputPorts)):
                    # This is an input. Do nothing
                    CompArgs.append(
                        self.inputPorts[LModel[InputLabel]].namewoid)
                else:
                    # This is an output. Add the appropriate component
                    # to the worklist if not already present
                    SourceComp = ProgList[LModel[InputLabel] -
                                          len(self.inputPorts)]
                    if (SourceComp not in VisitedSet):
                        WorkList.append(SourceComp)
                        VisitedSet.add(SourceComp)

                    CompArgs.append(SourceComp)

            RefinedProgList.append((CurComp, CompArgs))

        return RefinedProgList[::-1]

    # Converts a labeling to a program while eliminating dead code
    # LModel is {labelName: value in model, ...}
    def LValToProg(self, model):
        LModel = self.GetLModel(model)
        ProgList = self.ConstructProgramListing(LModel)
        RefinedProgList = self.RefineProgList(ProgList, LModel)

        for (Comp, CompArgs) in RefinedProgList:
            for i in range(len(CompArgs)):
                if isinstance(CompArgs[i], str):
                    pass
                else:
                    CompArgs[i] = CompArgs[i].outputPort.name

        # Now rename outputs and args appropriately
        RenameMap = {}
        NextTempID = 1
        for (Comp, CompArgs) in RefinedProgList:
            RenameMap[Comp.outputPort.name] = 'o_%02d' % NextTempID
            NextTempID += 1
        # Rename arguments
        for (Comp, CompArgs) in RefinedProgList:
            for i in range(len(CompArgs)):
                CompArgs[i] = RenameMap.get(CompArgs[i], CompArgs[i])
        # Generate the program

        Prog = ''
        for i in range(len(RefinedProgList)):
            Comp, CompArgs = RefinedProgList[i]
            OutputName = 'o_%02d' % (i + 1)
            Prog += Comp.Print(CompArgs, OutputName)
            Prog += '\n'
        return Prog

    def GenerateCircuitExpression(self, model):
        LModel = self.GetLModel(model)
        ProgList = self.ConstructProgramListing(LModel)
        RefinedProgList = self.RefineProgList(ProgList, LModel)

        RefinedProgList = RefinedProgList[::-1]

        tmpMap = {}
        for i in range(len(RefinedProgList)):
            (comp, _) = RefinedProgList[i]
            tmpMap[comp.outputPort.name] = i

        def GenerateSubexpr(i):
            (comp, compArgs) = RefinedProgList[i]
            production = comp.production

            if isinstance(production, list):
                opSym = production[0]
                retVal = '(%s' % opSym
                for compArg in compArgs:
                    retVal += ' '
                    retVal += GenerateSubexpr(tmpMap[compArg.outputPort.name])
                retVal += ')'
                return retVal

            elif isinstance(production, tuple):
                (constType, constVal) = production
                return '%s' % GetValFromType(constType, constVal).sexpr()

            elif isinstance(production, str):
                return production

            else:
                raise SynthException('Unknown type of production')


        funcRetType = self.synthFun[3]
        argList = self.synthFun[2]

        
        argListStr = ['(' + arg[0] + ' ' + GetStringFromType(arg[1]) + ')' for arg in argList]

        args = '(' + ' '.join(argListStr) + ')'


        return '(define-fun %s %s %s %s)' % (self.funcName, args,
                                             GetStringFromType(funcRetType),
                                             GenerateSubexpr(0))
