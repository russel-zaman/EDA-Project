##### ******************** EDA SUMMER PROJECT***************************
##### ******************** Submitted By:     ****************************
##    ******************* MD KAZI EBDUZZAMAN ****************************

## Project Name : Implementing a Netlist Equivalence Checker using SAT
## ## Usage : To check the Functional Equivalency of the Two different configurationed Digital Circuits
#             in gateLevel design (NetLists) according to the Formal Verification Theory. e.g Boolean Satisfiability (SAT)

#  ## Programm Method : -- Read two netlist Files as a Programm Arguments in any combination
#                       -- Build the appropriate CNF(List of List) based on the Characteristics Functions(CF) of the Boolean gates presented in the netlist files
#                       -- Solve the CNF according to Proposed Algorithm for SAT Check e.g DavisPutnam DP()
#                       -- After checking the both possibilities of the variable assignment(either 0/1) if the CNF array length = 1 then we assume  two Netlists 
#                          are functionally "Equivalent". for the case of array length 0 assumption will be "Not Equivalent" and print the input assignments 
#                          which leads the different output values as Counter Example.

import sys
import operator
import copy

## Provided Method for reading the netlist files to generate the necessary data
def readNetlist(file):
    nets = int(file.readline())
    inputs  = file.readline().split()
    inputs.sort()
    outputs = file.readline().split()
    outputs.sort()
    # read mapping
    mapping = {}
    while True:
        line = file.readline().strip()
        if not line:
            break
        net,name = line.split()
        mapping[name] = int(net)
    # read gates
    gates = []
    for line in file.readlines():
        bits = line.split()
        gate = bits.pop(0)
        ports = map(int,bits)
        gates.append((gate,[int(net) for net in ports]))
    return inputs,outputs,mapping,gates, nets

# read netlists
inputs1,outputs1,mapping1,gates1,netCount1 = readNetlist(open(sys.argv[1],"r"))
inputs2,outputs2,mapping2,gates2,netCount2 = readNetlist(open(sys.argv[2],"r"))
 
#add your code here!

## Printing the structure of the both Netlist files
print("Total NetCount_NetList_1", netCount1)
print("Inputs :\n", inputs1)
print("Outputs:\n", outputs1)
print("\nMapping (I/O to Net number)")
# For sorting the output according to dictionary key values 
for k, v in sorted(mapping1.items(), key=operator.itemgetter(0)):
    print(k+"\t",v)
print("\nGates :", gates1)
print("Printing the details of the Second Netlist")
print("\nTotal NetCount_NetList_2", netCount2)
print("Inputs :\n", inputs2)
print("Outputs:\n", outputs2)
for k, v in sorted(mapping2.items(), key=operator.itemgetter(0)):
    print(k+"\t",v)
print("\nGates :", gates2)

### To extract the I/O mapped net numbers of the variable names as a list from the Dictionary values obtained from two Netlist files
## For netlist1
#mapping_file1=list(sorted(mapping1.items(), key=operator.itemgetter(0)))
##print(mapping_file1)
#input_map1 = dict(mapping_file1[0:len(list(inputs1))])
## Obtained a list contained the mapped net numbers of Input variables of the first Netlist
#inputMappedNets_file1 = sorted(input_map1.values())
#output_map1 = dict(mapping_file1[len(list(inputs1)):])
## Obtained a list contained the mapped net numbers of Output variables of the first Netlist 
#outputMappedNets_file1 = list(sorted(output_map1.values()))
## For Netlist2
#mapping_file2=list(sorted(mapping2.items(), key=operator.itemgetter(0)))
##print(mapping_file2)
#input_map2 = dict(mapping_file2[0:len(list(inputs2))])
## Obtained a list contained the mapped net numbers of Input variables of the first Netlist
#inputMappedNets_file2 = [x+netCount1 for x in sorted(input_map2.values())]
#output_map2 = dict(mapping_file2[len(list(inputs2)):])
## Obtained a list contained the mapped net numbers of Input variables of the first Netlist
#outputMappedNets_file2 = [x+netCount1 for x in sorted(output_map2.values())]
##print(inputMappedNets_file1)
##print(outputMappedNets_file1)
##print(inputMappedNets_file2)
##print(outputMappedNets_file2)

#inputMappedNets_file1 = [v for k,v in mapping1.items() if k in inputs1]
#outputMappedNets_file1 = [v for k,v in mapping1.items() if k in outputs1]
#inputMappedNets_file2 = [v+netCount1 for k,v in mapping2.items() if k in inputs2]
#outputMappedNets_file2 = [v+netCount1 for k,v in mapping2.items() if k in outputs2]
#print(inputMappedNets_file1)
#print(outputMappedNets_file1)
#print(inputMappedNets_file2)
#print(outputMappedNets_file2)
inputMappedNets_file1 = []
inputMappedNets_file2=[]
for k1,v1 in mapping1.items():
    for k2,v2 in mapping2.items():
        if k1 in inputs1 and k2 in inputs2 and  k1==k2:
            
            mapping1[k1] = v1
            mapping2[k2] =v2
            inputMappedNets_file1.append(v1)
            inputMappedNets_file2.append(v2+netCount1)
print(inputMappedNets_file1)
print(inputMappedNets_file2)

outputMappedNets_file1 = []
outputMappedNets_file2 = []
for k1,v1 in mapping1.items():
    for k2,v2 in mapping2.items():
        if k1 in outputs1 and k2 in outputs2 and  k1==k2:
            
            mapping1[k1] = v1
            mapping2[k2] =v2
            outputMappedNets_file1.append(v1)
            outputMappedNets_file2.append(v2+netCount1)
print(outputMappedNets_file1)
print(outputMappedNets_file2)



## Declaring a method to form a list of Multiple Arrays based on the CF of Bol gates in netlist1
def buildCNF_Netlist1(booleanGates):
    cnf_net1 = []
    for bits in booleanGates:
        ports = bits[1]
        if bits[0] == 'and':
            # building the arrays of Literals for 3 Clauses for AND gate e.g. (a v ~c)(b v ~c)(~a v ~b v c)
            cnf_net1.append([ports[0],-ports[2]])
            cnf_net1.append([ports[1],-ports[2]])
            cnf_net1.append([-ports[0],-ports[1],ports[2]])
        elif bits[0] == 'or':
            # building the arrays of Literals for 3 Clauses for OR gate e.g. (~a v c)(~b v c)(a v b v ~c)
            cnf_net1.append([-ports[0],ports[2]])
            cnf_net1.append([-ports[1],ports[2]])
            cnf_net1.append([ports[0],ports[1],-ports[2]])
        elif bits[0] == 'inv':
            # building the arrays of Literals for 2 Clauses for NOT/INV gate e.g. (~a v ~b)(a v b)
            cnf_net1.append([-ports[0], -ports[1]])
            cnf_net1.append([ports[0],ports[1]])
        elif bits[0] == 'xor':
            # building the arrays of Literals for 4 Clauses for XOR gate e.g. (~a v ~b v ~c)(~a v b v c)(a v ~b v c)(a v b v ~c )
            cnf_net1.append([-ports[0],-ports[1],-ports[2]])
            cnf_net1.append([-ports[0],ports[1],ports[2]])
            cnf_net1.append([ports[0],-ports[1],ports[2]])
            cnf_net1.append([ports[0],ports[1],-ports[2]])
        else:
            print("\nInvalid Types of Gates !!!")
    return cnf_net1
initialCNF_Netlist1 = buildCNF_Netlist1(gates1)
#print(initialCNF_Netlist1)

## Declaring a method to form a list of Multiple Arrays based on the CF of Bol gates in netlist1
def buildCNF_Netlist2(booleanGates,uniqueValue):
    cnf_net2 = []
    for bits in booleanGates:
        ports = bits[1]
        # for second Netlist counting the net numbers of the gates will be started after the total netCounts of the first Netlist 
        ports = [x+uniqueValue for x in ports]
        if bits[0] == 'and':
            # building the arrays of Literals for AND, OR, INV & XOR gate respectively for netlist2 same as first
            cnf_net2.append([ports[0],-ports[2]])
            cnf_net2.append([ports[1],-ports[2]])
            cnf_net2.append([-ports[0],-ports[1],ports[2]])
        elif bits[0] == 'or':
            cnf_net2.append([-ports[0],ports[2]])
            cnf_net2.append([-ports[1],ports[2]])
            cnf_net2.append([ports[0],ports[1],-ports[2]])
        elif bits[0] == 'inv':
            cnf_net2.append([-ports[0], -ports[1]])
            cnf_net2.append([ports[0],ports[1]])
        elif bits[0] == 'xor':
            cnf_net2.append([-ports[0],-ports[1],-ports[2]])
            cnf_net2.append([-ports[0],ports[1],ports[2]])
            cnf_net2.append([ports[0],-ports[1],ports[2]])
            cnf_net2.append([ports[0],ports[1],-ports[2]])
        else:
            print ("Invalid Gates !!!")
    return cnf_net2
initialCNF_Netlist2 = buildCNF_Netlist2(gates2,netCount1)
#print(initialCNF_Netlist2)

## Declaring a method to build the Equivalent CF of the Input Mapped Nets of the Two Netlists
def buildEquivalentCNF(list1, list2):
    cnf = []
    for i in range(len(list1)):
        cnf.append([-list1[i], list2[i]])
        cnf.append([list1[i], -list2[i]])
    return cnf
EQCNF = buildEquivalentCNF(inputMappedNets_file1,inputMappedNets_file2)
print(EQCNF)

## Declaring a method to build the XOR CF of the Output Mapped Nets of the Two Netlists
def buildMieterCNF(list1, list2):
    cnf = []
    xorOut = netCount1+netCount2
    for i in range(len(list1)):
        xorOut += 1
        cnf.append([-list1[i], -list2[i], -xorOut])
        cnf.append([-list1[i], list2[i], xorOut])
        cnf.append([list1[i], -list2[i], xorOut])
        cnf.append([list1[i], list2[i], -xorOut])
    xorOut = netCount1+netCount2
    cnf1 = []
    for i in range(len(list1)): 
        xorOut += 1
        cnf1.extend([xorOut])
    cnf.append(cnf1)
    return cnf
MITCNF = buildMieterCNF(outputMappedNets_file1,outputMappedNets_file2)
print(MITCNF)
# Concatenating the four lists to obtain the final list of CNF
finalCNF = initialCNF_Netlist1+initialCNF_Netlist2+EQCNF+MITCNF
print("\n\nPrinting the Final CNF:\n\n {}".format(finalCNF))

## Declaring a method for solving the CNF by following approach:
## If any list in CNF contains positive Literal, then whole list will be removed from CNF while simultaneously from the other list 
## contains negative of that Literal; only that negative Literal will be removed from the list and vice versa
def solveCNF(cnf,singleLiteral):
    cnf = [list(filter(lambda x: x != -singleLiteral, i)) for i in cnf]
    for u in range(0, len(cnf), 1):
        for k in cnf:
            if k.count(singleLiteral):
                cnf.remove(k)
    return cnf

def counterExamplePrint_Netlist1(list,dictionary):
    for i in range(0,len(list),1):
        for k,v in dictionary.items():
            if v == -list[i]:
                print(k, " -> 1")
            elif v == list[i]:
                print(k, " -> 0")

def counterExamplePrint_Netlist2(list,dictionary):
    for j in range(0,len(list),1):
        for k,v in dictionary.items():
            v = v + netCount1
            if v == -list[j]:
                print(k, " -> 0")
            elif v == list[j]:
                print(k, " -> 1")

def DP(cnf):
    value = 0
    if value != 0:
        cnf = solveCNF(cnf, value)
    #equivalenceCheck = False    
    #cnfcopy = copy.deepcopy(cnf)
    #print("Printing the Lenght of Initial CNF: {}".format(len(cnf))) 
    #value = 0  
    #for z in range(0,len(cnf),1):
    while True:
        value=0
        for i in cnf:
            if len(i) == 1:
                value = i[0]
                #print("\nGet UNit Clause :{}".format(value))
                print("\nThe Length of CNF:{}".format(len(cnf)))
                cnf = solveCNF(cnf,value)
        #        print("Printing the Lenght of UNITRULE CNF: {}".format(len(cnf)))
        #        print("\nPrinting the Simplified CNF_UnitRULE : {}".format(cnf))
        ##        if len(i) == 1:
                break
        if value == 0:
            break
    
    #print(cnf)
    #for i in cnf:
    #    if len(i) == 1:
    #        value = i[0]
    #        print("\nGet UNit Clause :{}".format(value))
    #        cnf = solveCNF(cnf,value)
    #        for z in range(cnf.count(value)):
    #            cnf = solveCNF(cnf,value)
    #print("Printing the Lenght of UNITRULE CNF: {}".format(len(cnf)))
    #print("\nPrinting the Simplified CNF_UnitRULE : {}".format(cnf))

            
        
                
    # Check the Terminal Condition
    if len(cnf) == 0:
        print ("\n\n Solution Found !!! Terminate the algorithm")
        print("\nPrinting the Counter Example")
        counterExamplePrint_Netlist1(inputMappedNets_file1,mapping1)
        print("\n\n")
        counterExamplePrint_Netlist1(outputMappedNets_file1,mapping1)
        print("\n\n")
        counterExamplePrint_Netlist2(outputMappedNets_file2,mapping2)
        exit()
    for i in cnf:
        if len(i) == 0:
            #if len(cnf) != 1:
            #print("\nTemporary No Solution Possible!!! Finding more Approach !")
            return
    #if len(cnf) == 1:
    #        print("\nEquivalent")
    #        exit()  
    
    #else:
    
            #if len(cnf) != 1:
            #    print("\nTemporary No Solution Possible!!! Finding more Approach !")
            #    return
    
    if len(cnf) > 0:
        cnfcopy = copy.deepcopy(cnf)
       
    #value = cnf[-1][-1]       
        #print("\nGet the Right Most Literal:{}".format(value))
        cnf = solveCNF(cnf,-abs(cnf[-1][-1]))
        #print("Printing the Lenght of CNF: {}".format(len(cnf)))
        #print("\nPrintinf the CNF_Assignment_0 :{}".format(cnf))
        #print(cnf)
        cnfcopy = solveCNF(cnfcopy,abs(cnfcopy[-1][-1]))
        #print("Printing the Lenght of CNF: {}".format(len(cnf)))
        #print("\nPrinting the CNF_Assignment_1 :{}".format(cnfcopy))
        
        #print(cnfcopy)
    DP(cnf)
    
    DP(cnfcopy)

    
#DP(finalCNF)
print("\nEquivalent")








