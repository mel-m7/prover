"""
Describing Propositional Calculus Language, which includes:
Variables, Unification Terms, Functions, Predicates,
Negation (not), Disjunction (or), Conjunction (and),
Implication, Existential quantification (there exists),
Universal quantification (for all)

Created by: Meline Mkrtchyan
Date: May 2023
"""

from functools import reduce


"""
Base class for classes Variable and Term
"""
class Alphabet:
    def __init__(self, name):
        self.name = name
        self.time = 0

    def free_variables(self):
        pass

    def free_terms(self):
        pass

    def replace(self, current, new):
        return new if self == current else self

    def occurs(self, unification_term):
        return False

    def set_creation_time(self, time):
        self.time = time

    def __str__(self):
        return self.name


class Variable(Alphabet):
    def free_variables(self):
        return {self}

    def free_terms(self):
        return set()

    def __eq__(self, other):
        return isinstance(other, Variable) and self.name == other.name

    def __hash__(self):
        return hash(str(self))


class Term(Alphabet):
    def free_variables(self):
        return set()

    def free_terms(self):
        return {self}

    def occurs(self, unification_term):
        return self == unification_term

    def __eq__(self, other):
        return isinstance(other, Term) and self.name == other.name

    def __hash__(self):
        return hash(str(self))


"""
Base Class for Functor and Predicate
"""


class Formula:
    def __init__(self, name, terms):
        self.name = name
        self.terms = terms

    def free_variables(self):
        return (set() if len(self.terms) == 0
                else reduce((lambda x, y: x | y), [term.free_variables()
                                                   for term in self.terms]))

    def free_terms(self):
        return (set() if len(self.terms) == 0
                else reduce((lambda x, y: x | y), [term.free_terms()
                                                   for term in self.terms]))

    def occurs(self, unification_term):
        return any([term.occurs(unification_term) for term in self.terms])

    def set_creation_time(self, time):
        [term.set_creation_time(time) for term in self.terms]

    def __str__(self):
        if len(self.terms) == 0:
            return self.name
        return self.name + '(' + ', '.join(
            [str(term) for term in self.terms]
        ) + ')'

    def __eq__(self, other):
        return (self.name == other.name and
                len(self.terms) == len(other.terms) and
                all([self.terms[i] == other.terms[i] for i in range(len(self.terms))]))

    def __hash__(self):
        return hash(str(self))


class Functor(Formula):
    def __init__(self, name, terms):
        super().__init__(name, terms)
        self.time = 0

    def set_creation_time(self, time):
        super().set_creation_time(time)
        self.time = time

    def replace(self, current, new):
        return (new if self == current
                else Functor(self.name, [term.replace(current, new)
                                         for term in self.terms]))

    def __eq__(self, other):
        return isinstance(other, Functor) and super().__eq__(other)


class Predicate(Formula):
    def replace(self, current, new):
        return (new if self == current
                else Predicate(self.name, [term.replace(current, new)
                                           for term in self.terms]))

    def __eq__(self, other):
        return isinstance(other, Predicate) and super().__eq__(other)

    def __hash__(self):
        return hash(str(self))


class Not:
    def __init__(self, formula):
        self.formula = formula

    def free_variables(self):
        return self.formula.free_variables()

    def free_terms(self):
        return self.formula.free_terms()

    def replace(self, current, new):
        return new if self == current else Not(self.formula.replace(current, new))

    def occurs(self, term):
        return self.formula.occurs(term)

    def set_creation_time(self, time):
        self.formula.set_creation_time(time)

    def __eq__(self, other):
        return isinstance(other, Not) and self.formula == other.formula

    def __str__(self):
        return '¬' + str(self.formula)

    def __hash__(self):
        return hash(str(self))


class BinaryOperation:
    def __init__(self, formula1, formula2):
        self.formula1 = formula1
        self.formula2 = formula2

    def free_variables(self):
        return self.formula1.free_variables() | self.formula2.free_variables()

    def free_terms(self):
        return self.formula1.free_terms() | self.formula2.free_terms()

    def occurs(self, term):
        return self.formula1.occurs(term) or self.formula2.occurs(term)

    def set_creation_time(self, time):
        self.formula1.set_creation_time(time)
        self.formula2.set_creation_time(time)

    def __eq__(self, other):
        return (self.formula1 == other.formula1 and
                self.formula2 == other.formula2)

    def __hash__(self):
        return hash(str(self))


class And(BinaryOperation):
    def replace(self, current, new):
        return (new if self == current
                else And(self.formula1.replace(current, new),
                         self.formula2.replace(current, new)))

    def __eq__(self, other):
        return isinstance(other, And) and super().__eq__(other)

    def __str__(self):
        return '{} ∧ {}'.format(str(self.formula1), str(self.formula2))

    def __hash__(self):
        return hash(str(self))


class Or(BinaryOperation):
    def replace(self, current, new):
        return (new if self == current
                else Or(self.formula1.replace(current, new),
                        self.formula2.replace(current, new)))

    def __eq__(self, other):
        return isinstance(other, Or) and super().__eq__(other)

    def __str__(self):
        return '({} ∨ {})'.format(str(self.formula1), str(self.formula2))

    def __hash__(self):
        return hash(str(self))


class Implies(BinaryOperation):
    def replace(self, current, new):
        return (new if self == current
                else Implies(self.formula1.replace(current, new),
                             self.formula2.replace(current, new)))

    def __eq__(self, other):
        return isinstance(other, Implies) and super().__eq__(other)

    def __str__(self):
        return '({} → {})'.format(str(self.formula1), str(self.formula2))

    def __hash__(self):
        return hash(str(self))


"""
Quantification Base class for Universal and Existential Quantification
"""
class Quantification:
    def __init__(self, variable, formula):
        self.variable = variable
        self.formula = formula

    def free_variables(self):
        # free variables are all except the one under the quantification sign
        return self.formula.free_variables() - {self.variable}

    def free_terms(self):
        return self.formula.free_terms()

    def occurs(self, term):
        return self.formula.occurs(term)

    def set_creation_time(self, time):
        self.variable.set_creation_time(time)
        self.formula.set_creation_time(time)

    def __eq__(self, other):
        return (self.variable == other.variable and
                self.formula == other.formula)

    def __hash__(self):
        return hash(str(self))


class ForAll(Quantification):
    def replace(self, current, new):
        return new if self == current else ForAll(
            self.variable.replace(current, new),
            self.formula.replace(current, new))

    def __eq__(self, other):
        return isinstance(other, ForAll) and super().__eq__(other)

    def __str__(self):
        return '(∀{}. {})'.format(str(self.variable), str(self.formula))

    def __hash__(self):
        return hash(str(self))


class ThereExists(Quantification):
    def replace(self, current, new):
        return new if self == current else ThereExists(
            self.variable.replace(current, new),
            self.formula.replace(current, new))

    def __eq__(self, other):
        return isinstance(other, ThereExists) and super().__eq__(other)

    def __str__(self):
        return '(∃{}. {})'.format(str(self.variable), str(self.formula))

    def __hash__(self):
        return hash(str(self))
