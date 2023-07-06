"""
Automated Theorem Proving in Propositional Calculus
Created By: Meline Mkrtchyan
Date: May 2023
"""

from controller import *

def main():
    axioms = set()
    lemmas = {}
    controller(axioms, lemmas)


if __name__ == '__main__':
    print("""
        Automated theorem prover in Propositional Calculus(Logic)
        Author: Meline Mkrtchyan
        May 2023
        
        Logic Language Elements:
            x                   variable
            f(t1, t2, ...)      functor
            P(t1, t2, ...)      predicate, where t1, t2, ... are terms
            not A               negation
            A and B             conjunction
            A or B              disjunction
            A implies B         implication
            forall x. A(x)      universal quantification
            exists x. A(x)      existential quantification
            
        Commands to work with axioms and lemmas:
            axioms              lists all existing axioms
            lemmas              lists all existing lemmas
            axiom <formula>     adds formula to axioms' list
            lemma <formula>     proves and adds formula to lemmas' list
            remove <formula>    deletes formula
            reset               resets lists of axioms and lemmas
    """)
    main()
