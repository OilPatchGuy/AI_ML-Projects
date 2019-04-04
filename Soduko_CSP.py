"""Sudoku Solved as Constraint Satisfaction Problem

Reference (for CSP program used) : Artificial Intelligence, A Modern Approach by
Stuart Russel and Peter Norvig
 
 This is a bit messy but does the job
 
"""



#from utils import argmin_random_tie, count, first

#import search



from collections import defaultdict
import sys
import random



Sudoku = {}
Sudoku_keys ={}
Sudoku_keys2 ={}
nos =0
for row in ('A','B','C','D','E','F','G','H','I'):
    for col in range(1,10):
        nos += 1
        Sudoku_keys[row + str(col)] = nos
nos = 0       
for row in ('A','B','C','D','E','F','G','H','I'):
    for col in range(1,10):
        nos += 1
        Sudoku_keys2[nos] = row + str(col)
        
     

class CSP():

    """This class describes finite-domain Constraint Satisfaction Problems.

    A CSP is specified by the following inputs:

        variables   A list of variables; each is atomic (e.g. int or string).

        domains     A dict of {var:[possible_value, ...]} entries.

        neighbors   A dict of {var:[var,...]} that for each variable lists

                    the other variables that participate in constraints.

        constraints A function f(A, a, B, b) that returns true if neighbors

                    A, B satisfy the constraint when they have values A=a, B=b



    In the textbook and in most mathematical definitions, the

    constraints are specified as explicit pairs of allowable values,

    but the formulation here is easier to express and more compact for

    most cases. (For example, the n-Queens problem can be represented

    in O(n) space using this notation, instead of O(N^4) for the

    explicit representation.) In terms of describing the CSP as a

    problem, that's all there is.



    However, the class also supports data structures and methods that help you

    solve CSPs by calling a search function on the CSP. Methods and slots are

    as follows, where the argument 'a' represents an assignment, which is a

    dict of {var:val} entries:

        assign(var, val, a)     Assign a[var] = val; do other bookkeeping

        unassign(var, a)        Do del a[var], plus other bookkeeping

        nconflicts(var, val, a) Return the number of other variables that

                                conflict with var=val

        curr_domains[var]       Slot: remaining consistent values for var

                                Used by constraint propagation routines.

    The following methods are used only by graph_search and tree_search:

        actions(state)          Return a list of actions

        result(state, action)   Return a successor of state

        goal_test(state)        Return true if all constraints satisfied

    The following are just for debugging purposes:

        nassigns                Slot: tracks the number of assignments made

        display(a)              Print a human-readable representation

    """



    def __init__(self, variables, domains, neighbors, constraints):

        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""

        variables = variables or list(domains.keys())



        self.variables = variables

        self.domains = domains

        self.neighbors = neighbors

        self.constraints = constraints

        self.initial = ()

        self.curr_domains = None

        self.nassigns = 0
        #print (self.neighbors)


    def assign(self, var, val, assignment):

        """Add {var: val} to assignment; Discard the old value if any."""

        assignment[var] = val

        self.nassigns += 1



    def unassign(self, var, assignment):

        """Remove {var: val} from assignment.

        DO NOT call this if you are changing a variable to a new value;

        just call assign for that."""

        if var in assignment:

            del assignment[var]



    def nconflicts(self, var, val, assignment):

        """Return the number of conflicts var=val has with other variables."""

        # Subclasses may implement this more efficiently

        def conflict(var2):

            return (var2 in assignment and

                    not self.constraints(var, val, var2, assignment[var2]))

        return count(conflict(v) for v in self.neighbors[var])



    def display(self, assignment):

        """Show a human-readable representation of the CSP."""

        # Subclasses can print in a prettier way, or display with a GUI

        print('CSP:', self, 'with assignment:', assignment)



    # These methods are for the tree and graph-search interface:



    def actions(self, state):

        """Return a list of applicable actions: nonconflicting

        assignments to an unassigned variable."""

        if len(state) == len(self.variables):

            return []

        else:

            assignment = dict(state)

            var = first([v for v in self.variables if v not in assignment])

            return [(var, val) for val in self.domains[var]

                    if self.nconflicts(var, val, assignment) ==  0]



    def result(self, state, action):

        """Perform an action and return the new state."""

        (var, val) = action

        return state + ((var, val),)



    def goal_test(self, state):

        """The goal is to assign all variables, with all constraints satisfied."""

        assignment = dict(state)
        
        #print (assignment)

        return (len(assignment) == len(self.variables)

                and all(self.nconflicts(variables, assignment[variables], assignment) ==  0

                        for variables in self.variables))



    # These are for constraint propagation



    def support_pruning(self):

        """Make sure we can prune values from domains. (We want to pay

        for this only if we use it.)"""

        if self.curr_domains is None:

            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    


    def suppose(self, var, value):

        """Start accumulating inferences from assuming var=value."""

        self.support_pruning()

        removals = [(var, a) for a in self.curr_domains[var] if a != value]

        self.curr_domains[var] = [value]

        return removals



    def prune(self, var, value, removals):

        """Rule out var=value."""

       # print('v', var, self.curr_domains[var])
        self.curr_domains[var].remove(value)
        
        if removals is not None:

            removals.append((var, value))
            



    def choices(self, var):

        """Return all values for var that aren't currently ruled out."""

        return (self.curr_domains or self.domains)[var]



    def infer_assignment(self):

        """Return the partial assignment implied by the current inferences."""

        self.support_pruning()

        return {v: self.curr_domains[v][0]

                for v in self.variables if 1 == len(self.curr_domains[v])}



    def restore(self, removals):

        """Undo a supposition and all inferences from it."""

        for B, b in removals:

            self.curr_domains[B].append(b)



    # This is for min_conflicts search



    def conflicted_vars(self, current):

        """Return a list of variables in current assignment that are in conflict"""

        return [var for var in self.neighbors

                if self.nconflicts(var, current[var], current) > 0]





# Constraint Propagation with AC-3





def AC3(csp, queue=None, removals=None):

    """[Figure 6.3]"""

    if queue is None:

        queue = [(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]]
       

    csp.support_pruning()
    removals =[]
    while queue:

        (Xi, Xj) = queue.pop()
       # print("curr_domain ", csp.curr_domains)
        if revise(csp, Xi, Xj, removals):
            try:
                if not csp.curr_domains[Xi]:
                    return False
            except:
                return False

            for Xk in csp.neighbors[Xi]:

                if Xk != Xj:

                    queue.append((Xk, Xi))
    
    AC3_Result = {}
    for result in csp.curr_domains.keys():
        AC3_Result[result] = csp.curr_domains[result][0]
    #print("AC ", AC3_Result)
    
    if not csp.goal_test(AC3_Result):
        return False
    
    
    f = open("output.txt", "a")
    
    for j in range(1,82):
        if j in csp.variables:
            output = '%s' % (csp.curr_domains[j][0])
            f.write(output)
        else:
            output = '%s' % (csp.domains[j])
            f.write(output)
            
    output = '%s \n' %(" AC3")
    f.write(output)
    # f.close()
    return True





def revise(csp, Xi, Xj, removals):

    """Return true if we remove a value."""

    revised = False
    if Xi in csp.variables:
        for x in csp.curr_domains[Xi]:
            if Xj in csp.variables:
                if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
                    #print("pr1")
                    csp.prune(Xi, x, removals)
                    revised = True     
            else:
                if all(not csp.constraints(Xi, x, Xj, y) for y in csp.domains[Xj]):
                    #print("pr2")
                    csp.prune(Xi, x, removals)
                    revised = True
    else:
        if Xj in csp.variables:
            for x in csp.domains[Xi]:
                if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
                    #print("pr3")
                    csp.prune(Xi, x, removals)
                    revised = True
        else:
            for x in csp.domains[Xi]:
                if all(not csp.constraints(Xi, x, Xj, y) for y in csp.domains[Xj]):
                    #print("pr4")
                    csp.prune(Xi, x, removals)
                    revised = True
            
    return revised
    
# Map-Coloring Problems





class UniversalDict:

    """A universal dict maps any key to the same value. We use it here

    as the domains dict for CSPs in which all variables have the same domain.

    >>> d = UniversalDict(42)

    >>> d['life']

    42

    """



    def __init__(self, value): self.value = value



    def __getitem__(self, key): return self.value



    def __repr__(self): return '{{Any: {0!r}}}'.format(self.value)





def different_values_constraint(A, a, B, b):

    """A constraint saying two neighboring variables must differ in value."""
    return a != b

def SudokuCSP(deck):
    deck_list = list(deck)
    Changeable = {}
    Domain = {}
    numbers = '123456789'
    n = 0 
    for i in range(1,10):
        Sudoku['A' + str(i)] = str(deck_list[i-1])
        n +=1
        Domain[n] = str(deck_list[i-1])
        if(str(deck_list[i-1]) ==  '0'): 
            Changeable[n] = 'A' + str(i)
            Domain[n] = list(numbers)
            
    for i in range(1,10):
        Sudoku['B' + str(i)] = str(deck_list[i+ 8])
        n += 1
        Domain[n] = str(deck_list[i+ 8])
        if(str(deck_list[i+8]) ==  '0'):
            Changeable[n] ='B' + str(i)
            Domain[n] = list(numbers)
    
    for i in range(1,10):
        Sudoku['C' + str(i)] = str(deck_list[i+ 17])
        n += 1
        Domain[n] = str(deck_list[i+ 17])
        if(str(deck_list[i+17]) ==  '0'):
            Changeable[n] ='C' + str(i)
            Domain[n] = list(numbers)
    
    for i in range(1,10):
        Sudoku['D' + str(i)] = str(deck_list[i+ 26])
        n += 1
        Domain[n] = str(deck_list[i+ 26])
        if(str(deck_list[i+26]) ==  '0'):
            Changeable[n] ='D' + str(i)
            Domain[n] = list(numbers)
            
    for i in range(1,10):
        Sudoku['E' + str(i)] = str(deck_list[i+ 35])
        n += 1
        Domain[n] = str(deck_list[i+ 35])
        if(str(deck_list[i+35]) ==  '0'):
            Changeable[n] ='E' + str(i)
            Domain[n] = list(numbers)
            
    for i in range(1,10):
        Sudoku['F' + str(i)] = str(deck_list[i+ 44])
        n +=1
        Domain[n] = str(deck_list[i+ 44])
        if(str(deck_list[i+44]) ==  '0'):
            Changeable[n] ='F' + str(i)
            Domain[n] = list(numbers)
    
    for i in range(1,10):
        Sudoku['G' + str(i)] = str(deck_list[i+ 53])
        n += 1
        Domain[n] = str(deck_list[i+ 53])
        if(str(deck_list[i+53]) ==  '0'):
            Changeable[n] ='G' + str(i)
            Domain[n] = list(numbers)
            
    for i in range(1,10):
        Sudoku['H' + str(i)] = str(deck_list[i+ 62])
        n += 1
        Domain[n] = str(deck_list[i+ 62])
        if(str(deck_list[i+62]) ==  '0'):
            Changeable[n] = 'H' + str(i)
            Domain[n] = list(numbers)
            
    for i in range(1,10):
        Sudoku['I' + str(i)] = str(deck_list[i+ 71])
        n += 1
        Domain[n] = str(deck_list[i+ 71])
        if(str(deck_list[i+71]) ==  '0'):
            Changeable[n] ='I' + str(i)
            Domain[n] = list(numbers) 
  
    
    Neighbours = {}
    for token in Changeable.keys():
        Neighbours[token] = set()
    rows = ['A' , 'B', 'C', 'D','E','F','G','H','I']
    columns = ['1' , '2', '3', '4','5','6','7','8','9']
    corner1_rows = ['A' , 'B', 'C']
    corner1_columns = ['1' , '2', '3']
    corner2_rows = ['D','E','F']
    corner2_columns = ['1' , '2', '3']
    corner3_rows = ['G','H','I']
    corner3_columns = ['1' , '2', '3']
    corner4_rows = ['A' , 'B', 'C']
    corner4_columns = ['4' , '5', '6']
    corner5_rows = ['D','E','F']
    corner5_columns = ['4' , '5', '6']
    corner6_rows = ['G','H','I']
    corner6_columns = ['4' , '5', '6']
    corner7_rows = ['A' , 'B', 'C']
    corner7_columns = ['7' , '8', '9']
    corner8_rows = ['D','E','F']
    corner8_columns = ['7' , '8', '9']
    corner9_rows = ['G','H','I']
    corner9_columns = ['7' , '8', '9'] 

    for row in rows:
        for row1 in rows:
            if row != row1:
                for column in columns:
                    for chan in Changeable.keys():
                        if (Changeable[chan] == row+column):     
                            b = Neighbours[chan]
                            b.add(Sudoku_keys[row1 + column])
                            Neighbours[chan] = b
                    
                
    for column in columns:
        for column1 in columns:
            if column != column1:
                for  row in rows:
                    for chan in Changeable.keys():
                        if (Changeable[chan] == row+column):
                            b = Neighbours[chan]
                            b.add(Sudoku_keys[row + column1])
                            Neighbours[chan] =b
                    
    for row in corner1_rows:
        for column in corner1_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner1_rows:
                        for column1 in corner1_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
    for row in corner2_rows:
        for column in corner2_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner2_rows:
                        for column1 in corner2_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner3_rows:
        for column in corner3_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner3_rows:
                        for column1 in corner3_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner4_rows:
        for column in corner4_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner4_rows:
                        for column1 in corner4_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner5_rows:
        for column in corner5_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner5_rows:
                        for column1 in corner5_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner6_rows:
        for column in corner6_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner6_rows:
                        for column1 in corner6_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner7_rows:
        for column in corner7_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner7_rows:
                        for column1 in corner7_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner8_rows:
        for column in corner8_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner8_rows:
                        for column1 in corner8_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
    for row in corner9_rows:
        for column in corner9_columns:
            for chan in Changeable.keys():
                if (Changeable[chan] == row+column):
                    b = Neighbours[chan]
                    for row1 in corner9_rows:
                        for column1 in corner9_columns:
                            if row != row1 and column !=column1:
                                b.add(Sudoku_keys[row1 + column1])
                                Neighbours[chan] =b
                                
                                
    
                            
    return CSP(Changeable.keys(), Domain, Neighbours,different_values_constraint)

                            
                        
                      
            
            
             
      

 
  

def MapColoringCSP(colors, neighbors):

    """Make a CSP for the problem of coloring a map with different colors

    for any two adjacent regions. Arguments are a list of colors, and a

    dict of {region: [neighbor,...]} entries. This dict may also be

    specified as a string of the form defined by parse_neighbors."""

    if isinstance(neighbors, str):

        neighbors = parse_neighbors(neighbors)

    return CSP(list(neighbors.keys()), UniversalDict(colors), neighbors,

               different_values_constraint)





def parse_neighbors(neighbors, variables=None):

    """Convert a string of the form 'X: Y Z; Y: Z' into a dict mapping

    regions to neighbors. The syntax is a region name followed by a ':'

    followed by zero or more region names, followed by ';', repeated for

    each region name. If you say 'X: Y' you don't need 'Y: X'.

    >>> parse_neighbors('X: Y Z; Y: Z') == {'Y': ['X', 'Z'], 'X': ['Y', 'Z'], 'Z': ['X', 'Y']}

    True

    """

    dic = defaultdict(list)

    specs = [spec.split(':') for spec in neighbors.split(';')]

    for (A, Aneighbors) in specs:

        A = A.strip()

        for B in Aneighbors.split():

            dic[A].append(B)

            dic[B].append(A)

    return dic

# CSP Backtracking Search



# Variable ordering





def first_unassigned_variable(assignment, csp):

    """The default variable order."""

    return first([var for var in csp.variables if var not in assignment])





def mrv(assignment, csp):

    """Minimum-remaining-values heuristic."""

    return argmin_random_tie(

        [v for v in csp.variables if v not in assignment],

        key=lambda var: num_legal_values(csp, var, assignment))





def num_legal_values(csp, var, assignment):

    if csp.curr_domains:

        return len(csp.curr_domains[var])

    else:

        return count(csp.nconflicts(var, val, assignment) == 0

                     for val in csp.domains[var])



# Value ordering





def unordered_domain_values(var, assignment, csp):

    """The default value order."""

    return csp.choices(var)





def lcv(var, assignment, csp):

    """Least-constraining-values heuristic."""

    return sorted(csp.choices(var),

                  key=lambda val: csp.nconflicts(var, val, assignment))



# Inference





def no_inference(csp, var, value, assignment, removals):

    return True





def forward_checking(csp, var, value, assignment, removals):

    """Prune neighbor values inconsistent with var=value."""

    csp.support_pruning()

    for B in csp.neighbors[var]:
    
        if B in csp.variables:
            if B not in assignment:
    
                for b in csp.curr_domains[B][:]:
    
                    if not csp.constraints(var, value, B, b):
    
                        csp.prune(B, b, removals)
    
                if not csp.curr_domains[B]:

                    return False
        else:
            for b in csp.domains[B][:]:
    
                    if not csp.constraints(var, value, B, b):
                        
                        if var in csp.variables:
    
                            csp.prune(var,value, removals)
    
                            if not csp.curr_domains[var]:

                                return False

    return True





def mac(csp, var, value, assignment, removals):

    """Maintain arc consistency."""

    return AC3(csp, [(X, var) for X in csp.neighbors[var]], removals)



# The search, proper





def backtracking_search(csp,

                        select_unassigned_variable=mrv,

                        order_domain_values=unordered_domain_values,

                        inference=forward_checking):

    """[Figure 6.5]"""



    def backtrack(assignment):

        if len(assignment) == len(csp.variables):

            return assignment

        var = select_unassigned_variable(assignment, csp)
    

        for value in order_domain_values(var, assignment, csp):

            if 0 == csp.nconflicts(var, value, assignment):

                csp.assign(var, value, assignment)

                removals = csp.suppose(var, value)

                if inference(csp, var, value, assignment, removals):

                    result = backtrack(assignment)

                    if result is not None:

                        return result

                csp.restore(removals)

        csp.unassign(var, assignment)

        return None



    result = backtrack({})
    #print (result)

    assert result is None or csp.goal_test(result)
    f = open("output.txt", "a")
    
    for j in range(1,82):
        if j in csp.variables:
            output = '%s' % (result[j])
            f.write(output)
        else:
            output = '%s' % (csp.domains[j])
            f.write(output)
            
    output = '%s \n' %(" BTS")
    f.write(output)
    f.close()
            
    return result
def first(iterable, default=None):

    """Return the first element of an iterable or the next element of a generator; or default."""

    try:

        return iterable[0]

    except IndexError:

        return default

    except TypeError:

        return next(iterable, default)
        
def count(seq):

    """Count the number of items in sequence that are interpreted as true."""

    return sum(bool(x) for x in seq)
argmin = min
identity = lambda x: x
def argmin_random_tie(seq, key=identity):

    """Return a minimum element of seq; break ties at random."""
    return argmin(shuffled(seq), key=key)

def shuffled(iterable):

    """Randomly shuffle a copy of iterable."""

    items = list(iterable)

    random.shuffle(items)

    return items

Deck = sys.argv[1]    
Sudoku_deck = SudokuCSP(Deck)
Sudoku_result = AC3(Sudoku_deck)
if not Sudoku_result:
    Sudoku_result2 = backtracking_search(Sudoku_deck,mrv,lcv,forward_checking)  

