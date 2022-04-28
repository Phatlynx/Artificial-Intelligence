# 
# @file task2.py
# @author Kevin Hsieh
# @PeopleSoftID 2078611
# @professor Dr. Eick
# @brief COSC4368 - Problem Set 1 Task 2
# @version 6.1
# @date 2022-02-21
# @note This code is derived from the python-constraint library
# @copyright Copyright (c) 2022
# I implemented a recursive backtracking search for my CSP solver, it utilizes
# minimum-remaining-values(MRV) heuristic. If some variable X has no legal
# values left, the MRV heuristic will select X and failure will be detected
# immediately, avoiding pointless searches through other variables. It also does
# a generic form of inference called forward checking. Whenever a variable X is
# assigned, the forward-checking process establishes arc consistency for it: for
# each unassigned variable Y that is connected to X by a constraint, delete from
# Y’s domain any value that is inconsistent with the value chosen for X

from collections import OrderedDict
import copy
import csv

nva=0
class Problem(object):
    def __init__(self, solver=None):
        self._solver = solver
        self._constraints = []
        self._variables = {}

    def reset(self):
        del self._constraints[:]
        self._variables.clear()

    def setSolver(self, solver):
        self._solver = solver

    def getSolver(self):
        return self._solver

    def addVariable(self, variable, domain):
        if variable in self._variables:
            msg = "Tried to insert duplicated variable %s" % repr(variable)
            raise ValueError(msg)
        if hasattr(domain, "__getitem__"):
            domain = Domain(domain)
        elif isinstance(domain, Domain):
            domain = copy.copy(domain)
        else:
            msg = "Domains must be instances of subclasses of the Domain class"
            raise TypeError(msg)
        if not domain:
            raise ValueError("Domain is empty")
        self._variables[variable] = domain
            

    def addVariables(self, variables, domain):
        for variable in variables:
            self.addVariable(variable, domain)

    def addConstraint(self, constraint, variables=None):
        # Add a constraint to the problem
        if not isinstance(constraint, Constraint):
            if callable(constraint):
                constraint = FunctionConstraint(constraint)
            else:
                msg = (
                    "Constraints must be instances of subclasses "
                    "of the Constraint class"
                )
                raise ValueError(msg)
        self._constraints.append((constraint, variables))

    def getSolution(self):
        # Find and return a solution to the problem
        domains, constraints, vconstraints = self._getArgs()
        if not domains:
            return None
        return self._solver.getSolution(domains, constraints, vconstraints)

    def _getArgs(self):
        domains = self._variables.copy()
        allvariables = domains.keys()
        constraints = []
        for constraint, variables in self._constraints:
            if not variables:
                variables = list(allvariables)
            constraints.append((constraint, variables))
        vconstraints = {}
        for variable in domains:
            vconstraints[variable] = []
        for constraint, variables in constraints:
            for variable in variables:
                vconstraints[variable].append((constraint, variables))
        for constraint, variables in constraints[:]:
            constraint.preProcess(variables, domains, constraints, vconstraints)
        for domain in domains.values():
            domain.resetState()
            if not domain:
                return None, None, None
        return domains, constraints, vconstraints


# ----------------------------------------------------------------------
# Variables
# ----------------------------------------------------------------------
class Variable(object):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

Unassigned = Variable("Unassigned")

# ----------------------------------------------------------------------
# Domains
# ----------------------------------------------------------------------
class Domain(list):
    def __init__(self, set):
        list.__init__(self, set)
        self._hidden = []
        self._states = []

    def resetState(self):
        # Reset to the original domain state, including all possible values
        self.extend(self._hidden)
        del self._hidden[:]
        del self._states[:]

    def pushState(self):
        # Save current domain state
        self._states.append(len(self))

    def popState(self):
        # Restore domain state from the top of the stack
        diff = self._states.pop() - len(self)
        if diff:
            self.extend(self._hidden[-diff:])
            del self._hidden[-diff:]

    def hideValue(self, value):
        # Hide the given value from the domain
        list.remove(self, value)
        self._hidden.append(value)


class Solver(object):
    def getSolution(self, domains, constraints, vconstraints):
        msg = "%s is an abstract class" % self.__class__.__name__
        raise NotImplementedError(msg)


class RecursiveBacktrackingSolver(Solver):
    def __init__(self, forwardcheck=True):
        self._forwardcheck = forwardcheck

    def recursiveBacktracking(self, solutions, domains, vconstraints, assignments, single):
        # Minimum Remaing Values (MRV) heuristics
        global nva
        lst = [(-len(vconstraints[variable]), len(domains[variable]), variable) for variable in domains]
        lst.sort()
        for item in lst:
            if item[-1] not in assignments:
                # Found an unassigned variable.
                break
        else:
            # No unassigned variables. A solution is found
            solutions.append(assignments.copy())
            return solutions

        variable = item[-1]
        assignments[variable] = None

        forwardcheck = self._forwardcheck
        if forwardcheck:
            pushdomains = [domains[x] for x in domains if x not in assignments]
        else:
            pushdomains = None

        for value in domains[variable]:
            assignments[variable] = value
            nva+=1
            if pushdomains:
                for domain in pushdomains:
                    domain.pushState()
            for constraint, variables in vconstraints[variable]:
                if not constraint(variables, domains, assignments, pushdomains):
                    # Value is not good.
                    break
            else:
                # Value is good. Recurse and get next variable.
                self.recursiveBacktracking(solutions, domains, vconstraints, assignments, single)
                if solutions and single:
                    return solutions
            if pushdomains:
                for domain in pushdomains:
                    domain.popState()
        del assignments[variable]
        nva+=1
        return solutions

    def getSolution(self, domains, constraints, vconstraints):
        solutions = self.recursiveBacktracking([], domains, vconstraints, {}, True)
        return solutions and solutions[0] or None

# ----------------------------------------------------------------------
# Constraints
# ----------------------------------------------------------------------
class Constraint(object):
    # Abstract base class for constraints

    def preProcess(self, variables, domains, constraints, vconstraints):
        # Preprocess variable domains
        if len(variables) == 1:
            variable = variables[0]
            domain = domains[variable]
            for value in domain[:]:
                if not self(variables, domains, {variable: value}):
                    domain.remove(value)
            constraints.remove((self, variables))
            vconstraints[variable].remove((self, variables))

    def forwardCheck(self, variables, domains, assignments, _unassigned=Unassigned):
        unassignedvariable = _unassigned
        for variable in variables:
            if variable not in assignments:
                if unassignedvariable is _unassigned:
                    unassignedvariable = variable
                else:
                    break
        else:
            if unassignedvariable is not _unassigned:
                # Remove from the unassigned variable domain's all values which break contraints
                domain = domains[unassignedvariable]
                if domain:
                    for value in domain[:]:
                        assignments[unassignedvariable] = value
                        if not self(variables, domains, assignments):
                            domain.hideValue(value)
                    del assignments[unassignedvariable]
                if not domain:
                    return False
        return True


class FunctionConstraint(Constraint):
    # Constraint which wraps a function defining the constraint
    def __init__(self, func, assigned=True):
        self._func = func
        self._assigned = assigned

    def __call__(self,variables,domains,assignments,forwardcheck=False,_unassigned=Unassigned):
        parms = [assignments.get(x, _unassigned) for x in variables]
        missing = parms.count(_unassigned)
        if missing:
            return (self._assigned or self._func(*parms)) and (
                not forwardcheck
                or missing != 1
                or self.forwardCheck(variables, domains, assignments)
            )
        return self._func(*parms)


############################################################################################################################

def main(user_input):
    if(user_input=="a"):
        print("Problem A")
        problemA = Problem(RecursiveBacktrackingSolver())
        problemA.addVariables(["A","B","C","D","E","F"], list(range(1, 101)))

        def c1(A, B, C, E, F):
            return A == B + C + E + F

        def c2(D, E, F):
            return D == E + F + 21

        def c3(A, D, E):
            return D ** 2 == E * E * A + 694

        def c4(E, F, A):
            return E + F < A

        problemA.addConstraint(FunctionConstraint(c1), ["A", "B", "C", "E", "F"])
        problemA.addConstraint(FunctionConstraint(c2), ["D", "E", "F"])
        problemA.addConstraint(FunctionConstraint(c3), ["A", "D", "E"])
        problemA.addConstraint(FunctionConstraint(c4), ["E", "F", "A"])

        solutionA = problemA.getSolution()
        print(OrderedDict(sorted(solutionA.items())))
        print(solutionA)
        print("nva=",nva+len(solutionA))

        keysA, valuesA = [], []

        for key, value in solutionA.items():
            keysA.append(key)
            valuesA.append(value)       

        with open("values.csv", "w") as outfile:
            csvwriter = csv.writer(outfile)
            csvwriter.writerow(keysA)
            csvwriter.writerow(valuesA)
        print("----------------------------------------------------------------------------------------------------------")
    elif(user_input=="b"):
        print("Problem B")
        problemB = Problem(RecursiveBacktrackingSolver())
        problemB.addVariables(["A","B","C","D","E","F","G","H","I","J"],list(range(1, 101)))

        def c1(A, B, C, E, F):
            return A == B + C + E + F

        def c2(D, E, F):
            return D == E + F + 21

        def c3(A, D, E):
            return D ** 2 == E * E * A + 694

        def c4(E, F, A):
            return E + F < A
        def c5(H, J, E, G, I):
            return H * J + E * 16 == (G + I) ** 2 - 48

        def c6(A, C, H, F):
            return A - C == (H - F) ** 2 + 4

        def c7(J, G):
            return 4 * J == G ** 2 + 7

        problemB.addConstraint(FunctionConstraint(c1), ["A", "B", "C", "E", "F"])
        problemB.addConstraint(FunctionConstraint(c2), ["D", "E", "F"])
        problemB.addConstraint(FunctionConstraint(c3), ["A", "D", "E"])
        problemB.addConstraint(FunctionConstraint(c4), ["E", "F", "A"])
        problemB.addConstraint(FunctionConstraint(c5), ["H", "J", "E", "G", "I"])
        problemB.addConstraint(FunctionConstraint(c6), ["A", "C", "H", "F"])
        problemB.addConstraint(FunctionConstraint(c7), ["J", "G"])

        solutionB = problemB.getSolution()
        print(OrderedDict(sorted(solutionB.items())))
        print("nva=",nva)

        keysB, valuesB = [], []

        for key, value in solutionB.items():
            keysB.append(key)
            valuesB.append(value)       


        with open("values.csv", "a") as outfile:
            csvwriter = csv.writer(outfile)
            csvwriter.writerow(keysB)
            csvwriter.writerow(valuesB)
        print("----------------------------------------------------------------------------------------------------------")
    else:
        print("Problem C")
        problemC = Problem(RecursiveBacktrackingSolver())
        problemC.addVariables(["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O"],list(range(1, 101)))

        def c1(A, B, C, E, F):
            return A == B + C + E + F

        def c2(D, E, F):
            return D == E + F + 21

        def c3(A, D, E):
            return D ** 2 == E * E * A + 694

        def c4(E, F, A):
            return E + F < A
        def c5(H, J, E, G, I):
            return H * J + E * 16 == (G + I) ** 2 - 48

        def c6(A, C, H, F):
            return A - C == (H - F) ** 2 + 4

        def c7(J, G):
            return 4 * J == G ** 2 + 7
        def c8(M, K):
            return 2 * M == K ** 2 - 25

        def c9(N, O, J, F):
            return (N - O) ** 2 == (J - F) * O * 2

        def c10(N, M, J):
            return N ** 2 == M * J + 100

        def c11(L, N, G, B, F, K, M):
            return (L + N) ** 2 + 1875 == G * (B + F) * (K + M + N + 30)

        def c12(L, O, A, K, G):
            return L * O == (A ** 2) * (K - G)

        def c13(L, M, O, F, A):
            return L ** 3 == M ** 2 - (O * F * A)

        problemC.addConstraint(FunctionConstraint(c1), ["A", "B", "C", "E", "F"])
        problemC.addConstraint(FunctionConstraint(c2), ["D", "E", "F"])
        problemC.addConstraint(FunctionConstraint(c3), ["A", "D", "E"])
        problemC.addConstraint(FunctionConstraint(c4), ["E", "F", "A"])
        problemC.addConstraint(FunctionConstraint(c5), ["H", "J", "E", "G", "I"])
        problemC.addConstraint(FunctionConstraint(c6), ["A", "C", "H", "F"])
        problemC.addConstraint(FunctionConstraint(c7), ["J", "G"])
        problemC.addConstraint(FunctionConstraint(c8), ["M", "K"])
        problemC.addConstraint(FunctionConstraint(c9), ["N", "O", "J", "F"])
        problemC.addConstraint(FunctionConstraint(c10), ["N", "M", "J"])
        problemC.addConstraint(FunctionConstraint(c11), ["L", "N", "G", "B", "F", "K", "M"])
        problemC.addConstraint(FunctionConstraint(c12), ["L", "O", "A", "K", "G"])
        problemC.addConstraint(FunctionConstraint(c13), ["L", "M", "O", "F", "A"])

        solutionC = problemC.getSolution()
        print(OrderedDict(sorted(solutionC.items())))
        print("nva=",nva)

        keysC, valuesC = [], []
        for key, value in solutionC.items():
            keysC.append(key)
            valuesC.append(value)       

        with open("values.csv", "a") as outfile:
            csvwriter = csv.writer(outfile)
            csvwriter.writerow(keysC)
            csvwriter.writerow(valuesC)
        print("----------------------------------------------------------------------------------------------------------")

print('Which problem would you like to solve with CSP? (a, b, or c)')
user_input=input()
main(user_input)