"""
K-Induction Method

Based on:
Mary Sheeran, Satnam Singh, and Gunnar Stälmarck.
Checking safety properties using induction and a SAT-solver. 
FMCAD 2000

Adapted for Petri nets

This file is part of uSMPT.

uSMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

uSMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with uSMPT. If not, see <https://www.gnu.org/licenses/>.
"""

from __future__ import annotations

__author__ = "Nicolas AMAT, ONERA/DTIS, Université de Toulouse"
__contact__ = "nicolas.amat@onera.fr"
__license__ = "GPLv3"
__version__ = "1.0"

from logging import info
from multiprocessing import Queue
from typing import Optional

from usmpt.checkers.abstractchecker import AbstractChecker
from usmpt.exec.utils import set_verbose
from usmpt.interfaces.z3 import Z3
from usmpt.ptio.formula import Formula
from usmpt.ptio.ptnet import PetriNet
from usmpt.ptio.verdict import Verdict


class KInduction(AbstractChecker):
    """ k-induction method.

    Attributes
    ----------
    ptnet : PetriNet
        Initial Petri net.
    formula : Formula
        Reachability formula.
    induction_queue : Queue of int, optional
        Queue for the exchange with BMC.
    solver : Z3
        SMT solver (Z3).
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, verbose: bool = False, debug: bool = False, induction_queue: Optional[Queue[int]] = None, solver_pids: Optional[Queue[int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Initial Petri net.
        formula : Formula
            Reachability formula.
        debug : bool, optional
            Debugging flag.
        induction_queue : Queue of int, optional
            Queue for the exchange with k-induction.
        solver_pids : Queue of int, optional
            Queue to share the current PID.
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Formula to study
        self.formula: Formula = formula

        # Verbosity
        self.verbose : bool = verbose

        # Queue shared with BMC
        self.induction_queue: Optional[Queue[int]] = induction_queue

        # SMT solver
        self.solver: Z3 = Z3(debug=debug, solver_pids=solver_pids)

    def prove(self, result: Queue[Verdict], concurrent_pids: Queue[list[int]]) -> None:
        """ Prover.

        Parameters
        ----------
        result : Queue of Verdict
            Not used.
        concurrent_pids : Queue of int
            Not used.
        """
        set_verbose(self.verbose)

        info("[K-INDUCTION] RUNNING")

        iteration = self.prove_helper()

        if not self.solver.aborted and self.induction_queue is not None:
            self.induction_queue.put(iteration)

        # Kill the solver
        self.solver.kill()

    ######################
    # TODO: Sect. 2.3.3. #
    ######################
    def prove_helper(self) -> int:
        """ Prover to complete.

        Returns
        -------
        int
            Iteration number of the unsat query.
        """
        iteration = 0

        # Declare variables for the initial marking (iteration 0)
        self.solver.write(self.ptnet.smtlib_declare_places(0))
        self.solver.write(self.ptnet.smtlib_set_initial_marking(0))

        # Construct the base formula ψ_0 (neg(F(x0)) ∧ T(x0, x1))
        self.solver.push()
        self.solver.write(self.formula.smtlib(0, assertion=True, negation=True))  # Assert ¬F(x0)
        self.solver.write(self.ptnet.smtlib_declare_places(1))
        self.solver.write(self.ptnet.smtlib_transition_relation(0, 1))  # Assert T(x0, x1)

        # Assert F(x1) and check satisfiability
        self.solver.push()
        self.solver.write(self.formula.smtlib(1, assertion=True))  # Assert F(x1)
        if not self.solver.check_sat():
            self.solver.pop()
            self.solver.pop()
            return iteration  # UNSAT for ψ_0 ∧ F(x1)
        self.solver.pop()

        # Start K-Induction loop
        while True:
            iteration += 1

            # Declare new variables for next marking (iteration k + 1)
            self.solver.write(self.ptnet.smtlib_declare_places(iteration + 1))

            # Extend ψ_i with neg(F(x_i)) ∧ T(x_i, x_i+1)
            self.solver.write(self.formula.smtlib(iteration, assertion=True, negation=True))  # Assert ¬F(x_k)
            self.solver.write(self.ptnet.smtlib_transition_relation(iteration, iteration + 1))  # Assert T(x_k, x_k+1)

            # Check satisfiability of ψ_i ∧ F(x_{i+1})
            self.solver.push()
            self.solver.write(self.formula.smtlib(iteration + 1, assertion=True))  # Assert F(x_{k+1})
            if not self.solver.check_sat():
                self.solver.pop()
                self.solver.pop()
                return iteration  # UNSAT for ψ_i ∧ F(x_{k+1})
            self.solver.pop()

            

    