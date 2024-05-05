import sys
import random
import time
import math
import textwrap
from pprint import pprint
from dataclasses import dataclass
from typing import List, Set, Tuple, Optional, Iterator
from collections import defaultdict

# frozen to be hashable
## Dataclasses for representing literals, clauses, formulas, and assignments
@dataclass(frozen=True)
class Literal:
    variable: int
    negation: bool

    def __repr__(self):
    # Return a string representation of the literal, showing if it's negated.
        if self.negation:
            return '¬' + str(self.variable)
        else:
            return str(self.variable)

    def neg(self) -> 'Literal':
        # Return the negation of this literal.
        return Literal(self.variable, not self.negation)

@dataclass
class Clause:
    literals: List[Literal]

    def __repr__(self):
        # Return a string representation of the clause as a disjunction of literals.
        return '∨'.join(map(str, self.literals))

    def __iter__(self) -> Iterator[Literal]:
        
        return iter(self.literals)

    def __len__(self):
        
        return len(self.literals)

    def __hash__(self):
        x = 0 
        for lit in self.literals:
            x ^= hash(lit)
        return x

@dataclass
class Formula:
    clauses: List[Clause]
    __variables: Set[int]

    def __init__(self, clauses: List[Clause]):
        """
        Remove duplicate literals in clauses.
        """
        self.clauses = []
        self.__variables = set()
        for clause in clauses:
            self.clauses.append(Clause(list(set(clause))))
            for lit in clause:
                var = lit.variable
                self.__variables.add(var)

    def variables(self) -> Set[int]:
        """
        Return the set of variables contained in this formula.
        """
        return self.__variables

    def __repr__(self):
        return '∧'.join(f'({clause})' for clause in self.clauses)

    def __iter__(self) -> Iterator[Clause]:
        return iter(self.clauses)

    def __len__(self):
        return len(self.clauses)

@dataclass
class Assignment:
    value: bool
    antecedent: Optional[Clause]
    dl: int  # decision level

class Assignments(dict):
    """
    The assignments, also stores the current decision level.
    """
    def __init__(self):
        super().__init__()

        # the decision level
        self.dl = 0

        # Variable activities for VSIDS
        self.var_activities = {}

    def increment_activity(self, variable: int, increment: float):
        """
        Increment the activity of a variable.
        """
        if variable not in self.var_activities:
            self.var_activities[variable] = 0.0
        self.var_activities[variable] += increment

    def value(self, literal: Literal) -> bool:
        """
        Return the value of the literal with respect the current assignments.
        """
        if literal.negation:
            return not self[literal.variable].value
        else:
            return self[literal.variable].value

    def assign(self, variable: int, value: bool, antecedent: Optional[Clause]):
        # Assign a value to a variable at the current decision level with an antecedent clause.
        self[variable] = Assignment(value, antecedent, self.dl)

    def unassign(self, variable: int):
        # Remove an assignment from a variable.
        self.pop(variable)

    def satisfy(self, formula: Formula) -> bool:
        """
        Check whether the assignments actually satisfies the formula. 
        """
        for clause in formula:
            if True not in [self.value(lit) for lit in clause]:
                return False

        return True

def init_watches(formula: Formula):
    """
    Return lit2clauses and clause2lits
    """
    
    lit2clauses = defaultdict(list)
    clause2lits = defaultdict(list)
    
    for clause in formula:
        if len(clause) == 0:
            # Skip empty clauses
            continue
        elif len(clause) == 1:
            # For unit clause, we watch the only literal
            lit2clauses[clause.literals[0]].append(clause)
            clause2lits[clause].append(clause.literals[0])
        else:
            # For other clause, we choose any 2 literals to watch
            lit2clauses[clause.literals[0]].append(clause)
            lit2clauses[clause.literals[1]].append(clause)
            clause2lits[clause].append(clause.literals[0])
            clause2lits[clause].append(clause.literals[1])
            
    return lit2clauses, clause2lits

def cdcl_solve(formula: Formula) -> Optional[Assignments]:
    """
    Solve the CNF formula.
    If SAT, return the assignments.
    If UNSAT, return None.
    """
    start_time = time.time()  # Record the start time
    assignments = Assignments()
    lit2clauses, clause2lits = init_watches(formula)
    conflict_count = 0
    first_arithmetic_term = 1000
    common_difference = 1000
    difference_increment = 0
    
    unitclauses = [clause for clause in formula if len(clause) == 1]
    topropagate = []
    for clause in unitclauses:
        lit = clause.literals[0]
        var = lit.variable
        val = not lit.negation
        if var not in assignments:
            assignments.assign(var, val, clause)
            topropagate.append(lit)
    
    reason, clause = unitpropagation(assignments, lit2clauses, clause2lits, topropagate)
    if reason == 'conflict':
        return None

    # Main loop to assign values to variables.
    while not all_variables_assigned(formula, assignments):
        if time.time() - start_time > 90:  # Check if 90 seconds have passed
            print("Process terminated: Taking longer than 90 seconds.")
            raise SystemExit  # Terminate the process
        
        var, val = branchingVariablePick(formula, assignments)
        assignments.dl += 1
        assignments.assign(var, val, antecedent=None)
        topropagate = [Literal(var, not val)]
        while True:
            reason, clause = unitpropagation(assignments, lit2clauses, clause2lits, topropagate)
            if reason != 'conflict':
                break
                
            # Handle conflicts by learning new clauses and restarting.
            conflict_count += 1
            # Update activity scores of variables involved in the conflict
            max_dl = max(assignments[lit.variable].dl for lit in clause)
            for lit in clause:
                var = lit.variable
                if var in assignments:
                    assignments.increment_activity(var, 1.0 / (math.pow(0.95, max_dl)))
            
            # Handle conflicts by learning new clauses and restarting.
            if conflict_count >= first_arithmetic_term + difference_increment * common_difference:
                assignments = Assignments()
                lit2clauses, clause2lits = init_watches(formula)
                conflict_count = 0
                difference_increment += 1
                print("Restarted")
                break

            b, learntClause = conflict_analysis(clause, assignments)
            if b < 0:
                return None
            
            learntClauseAdd(formula, learntClause, assignments, lit2clauses, clause2lits)
            backtrack(assignments, b)
            assignments.dl = b
            literal = next(literal for literal in learntClause if literal.variable not in assignments)
            var = literal.variable
            val = not literal.negation
            assignments.assign(var, val, antecedent=learntClause)
            topropagate = [Literal(var, not val)]

    return assignments # Return assignments if the formula is satisfiable.


# Add learnt clauses
def learntClauseAdd(formula, clause, assignments, lit2clauses, clause2lits):
    formula.clauses.append(clause)
    for lit in sorted(clause, key=lambda lit: -assignments[lit.variable].dl):
        if len(clause2lits[clause]) < 2:
            clause2lits[clause].append(lit)
            lit2clauses[lit].append(clause)
        else:
            break


def all_variables_assigned(formula: Formula, assignments: Assignments) -> bool:
    return len(formula.variables()) == len(assignments)

# Pick variable for DECIDE
def branchingVariablePick(formula: Formula, assignments: Assignments) -> Tuple[int, bool]:
    """
    VSIDS heuristic for variable selection.
    """
    unassigned_vars = {var: 0.0 for var in formula.variables() if var not in assignments}
    
    # Compute variable activities based on the number of times they appeared in conflicts
    for clause in formula.clauses:
        max_dl_literals = [assignments[lit.variable].dl for lit in clause if lit.variable in assignments]
        max_dl = max(max_dl_literals) if max_dl_literals else 0
        for lit in clause:
            var = lit.variable
            if var in unassigned_vars:
                unassigned_vars[var] += 1.0 / (math.pow(0.95, max_dl))
    
    # Select the variable with the highest activity score
    var, activity = max(unassigned_vars.items(), key=lambda item: item[1])
    val = random.choice([True, False])
    return (var, val)

# BACKTRACK if conclict occurs
def backtrack(assignments: Assignments, b: int):
    to_remove = []
    for var, assignment in assignments.items():
        if assignment.dl > b:
            to_remove.append(var)
            
    for var in to_remove:
        assignments.pop(var)

def clause_status(clause: Clause, assignments: Assignments) -> str:
    """
    Return the status of the clause with respect to the assignments.

    There are 4 possible status of a clause:
      1. Unit - All but one literal are assigned False
      2. Unsatisfied - All literals are assigned False
      3. Satisfied - All literals are assigned True
      4. Unresolved - Neither unit, satisfied nor unsatisfied
    """
    values = []
    for literal in clause:
        if literal.variable not in assignments:
            values.append(None)
        else:
            values.append(assignments.value(literal))

    if True in values:
        return 'satisfied'
    elif values.count(False) == len(values):
        return 'unsatisfied'
    elif values.count(False) == len(values) - 1:
        return 'unit'
    else:
        return 'unresolved'

# Performs unit propagation using the watched literal data structures
def unitpropagation(assignments, lit2clauses, clause2lits, topropagate: List[Literal]) -> Tuple[str, Optional[Clause]]:
    while len(topropagate) > 0:
        watching_lit = topropagate.pop().neg()

        # use list(.) to copy it because size of 
        # lit2clauses[watching_lit]might change during for-loop
        watching_clauses = list(lit2clauses[watching_lit])
        for watching_clause in watching_clauses:
            for lit in watching_clause:
                if lit in clause2lits[watching_clause]:
                    # lit is another watching literal of watching_clause
                    continue
                elif lit.variable in assignments and assignments.value(lit) == False:
                    # lit is a assigned False
                    continue
                else:
                    # lit is not another watching literal of watching_clause
                    # and is non-False literal, so we rewatch it. (case 1)
                    clause2lits[watching_clause].remove(watching_lit)
                    clause2lits[watching_clause].append(lit)
                    lit2clauses[watching_lit].remove(watching_clause)
                    lit2clauses[lit].append(watching_clause)
                    break
            else:
                # we cannot find another literal to rewatch (case 2,3,4)
                watching_lits = clause2lits[watching_clause]
                if len(watching_lits) == 1:
                    # watching_clause is unit clause, and the only literal
                    # is assigned False, thus indicates a conflict
                    return ('conflict', watching_clause)
               	
                # the other watching literal
                other = watching_lits[0] if watching_lits[1] == watching_lit else watching_lits[1]
                if other.variable not in assignments:
                    # the other watching literal is unassigned. (case 3)
                    assignments.assign(other.variable, not other.negation, watching_clause)
                    topropagate.insert(0, other)
                elif assignments.value(other) == True:
                    # the other watching literal is assigned True. (case 2)
                    continue
                else:
                    # the other watching literal is assigned False. (case 4)
                    return ('conflict', watching_clause)

    return ('unresolved', None)

def resolve(a: Clause, b: Clause, x: int) -> Clause:
    #Resolve two clauses on a variable x, removing x from the resulting clause.
    result = set(a.literals + b.literals) - {Literal(x, True), Literal(x, False)}
    result = list(result)
    return Clause(result)

def conflict_analysis(clause: Clause, assignments: Assignments) -> Tuple[int, Clause]:
    """
    Analyze a conflict and return the backtrack level and the learnt clause.
    """
    if assignments.dl == 0:
        return (-1, None)
 
    # literals with current decision level
    literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]
    while len(literals) != 1:
        # implied literals
        literals = filter(lambda lit: assignments[lit.variable].antecedent != None, literals)

        # select any literal that meets the criterion
        literal = next(literals)
        antecedent = assignments[literal.variable].antecedent
        clause = resolve(clause, antecedent, literal.variable)

        # literals with current decision level
        literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]

    # out of the loop, `clause` is now the new learnt clause
    # compute the backtrack level b (second largest decision level)
    decisionlevels = sorted(set(assignments[literal.variable].dl for literal in clause))
    if len(decisionlevels) <= 1:
        return 0, clause
    else:
        return decisionlevels[-2], clause

def parse_dimacs_cnf(content: str) -> Formula:
    """
    parse the DIMACS cnf file format into corresponding Formula.
    """
    clauses = [Clause([])]
    num_vars = 0
    num_clauses = 0
    
    for line in content.splitlines():
        # Skip comment lines
        if line.startswith('c'):
            continue
        tokens = line.split()
        if len(tokens) != 0 and tokens[0] == 'p':
            num_vars = int(tokens[2])
            num_clauses = int(tokens[3])
        elif len(tokens) != 0 and tokens[0] not in ("p", "c"):
            for tok in tokens:
                lit = int(tok)
                if lit == 0:
                    clauses.append(Clause([]))
                else:
                    var = abs(lit)
                    neg = lit < 0
                    clauses[-1].literals.append(Literal(var, neg))

    # Handle the case where there are no variables and the only clause is an empty clause
    if num_vars == 0 and num_clauses == 1 and len(clauses) == 1 and len(clauses[0]) == 0:
        return Formula([Clause([])])

    if len(clauses[-1]) == 0:
        clauses.pop()

    return Formula(clauses)

if __name__ == '__main__':
    # you might comment it to get inconsistent execution time
    random.seed(5201314)

    start_time = time.time()

    if len(sys.argv) != 2:
        print('Provide one DIMACS cnf filename as argument.')
        sys.exit(1)
        
    dimacs_cnf = open(sys.argv[1]).read()
    formula = parse_dimacs_cnf(dimacs_cnf)
    result = cdcl_solve(formula)

    end_time = time.time()
    execution_time = end_time - start_time

    if result:
        assert result.satisfy(formula)
        print(f"Execution time: {execution_time:.2f} seconds")
        print('Formula is SAT with assignments:')
        assignments = sorted((var, assignment.value) for var, assignment in result.items())
        assignment_strings = [f"{var}: {value}" for var, value in assignments]
        wrapped_assignments = textwrap.wrap(', '.join(assignment_strings), width=80)
        print('\n'.join(wrapped_assignments))
    else:
        print(f"Execution time: {execution_time:.2f} seconds")
        print('Formula is UNSAT.')