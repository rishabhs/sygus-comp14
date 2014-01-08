# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# component.py contains the data structure definitions used for 
# internal representation of component based synthesis problem

import sys
from z3 import Const

if __name__ == "__main__":
    print 'This module is only intended to be used as a library!\n'
    sys.exit(1)
    
    
class SynthException(Exception):
    def __init__(self, ErrMsg):
        self.ErrMsg = ErrMsg

    def __repr__(self):
        """
        Some exception

        :return:
        """
        return '<SynthException: %s>' % self.ErrMsg

    def __str__(self):
        return 'Synthesis Exception. Error Message: %s' % self.ErrMsg

class Port:
    numPorts = 0
    def __init__(self, name, breed, sort):
        self.id = Port.numPorts
        Port.numPorts += 1
        self.name = '%s_%d' % (name, self.id)
        self.namewoid = name
        self.breed = breed
        self.sort = sort
        self.var = Const(self.name, self.sort)
    
    def __repr__(self):
        return 'Port_%s_%s' % (self.name, self.breed)
    
    def __str__(self):
        return 'Port_%s_%s' % (self.name, self.breed)
    
    def GenVarCopyForIteration(self, iteration):
        varCopyName= '%s_iter%d' % (self.name, iteration)
        return Const(varCopyName, self.sort)
    
    def GetNameWithoutId(self):
        return self.namewoid
        
    
class Component:
    numComponents = 0
    def __init__(self, inputPorts, outputPort, spec, name, production):
        self.inputPorts = inputPorts
        self.outputPort = outputPort
        self.spec = spec
        self.name = '%s_%d' % (name, Component.numComponents)
        Component.numComponents += 1
        self.production = production
        
    def GetName(self):
        return self.name
    
    def GetIndexedName(self):
        return self.name
    
    def __repr__(self):
        retVal = '<Component %s:' % (self.name)
        for port in self.inputPorts:
            retVal += '\n\t%r' % port
        retVal += '\n\t->'
        retVal += '\n\t%r' % self.outputPort
        retVal += '\n\tSpec\n\t%s\n' % self.spec
        retVal += '>'
        return retVal
    
    def SetInputLabels(self, labels):
        if len(labels) != len(self.inputPorts):
            raise SynthException('len(Labels) != len(self.InputPorts) in Component.SetInputLabels')
        self.inputLabels = labels
        self.inputLabelMap = {self.inputPorts[i].name: labels[i] for i in range(len(labels))}

    def SetOutputLabel(self, label):
        self.outputLabel = label
        
    def SetPosition(self, pos):
        self.pos = pos
        
    def Print(self, inputNames, outputName):
        retVal = '%s := %s(' % (outputName, self.name)
        for i in range(len(inputNames)):
            retVal += '%s' % inputNames[i]
            if (i != len(inputNames) - 1):
                retVal += ', '
        retVal += ')'
        return retVal

    def PrintExpr(self, args):
        if isinstance(self.production, list):
            retVal = '(synth-fun %s' % production[0]
            for arg in args:
                retVal += ' '
                retVal += arg
            retVal += ')'
            return retVal
        elif isinstance(self.production, tuple):
            if len(args) != 0:
                raise SynthException('Constant cannot have arguments')
            (constType, constVal) = self.production
            
