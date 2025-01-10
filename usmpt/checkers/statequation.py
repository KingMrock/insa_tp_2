"""
State Equation Method

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
from usmpt.exec.utils import STOP, send_signal_pids, set_verbose
from usmpt.interfaces.z3 import Z3
from usmpt.ptio.formula import Formula
from usmpt.ptio.ptnet import PetriNet
from usmpt.ptio.verdict import Verdict


class StateEquation(AbstractChecker):
    """ State equation method.
    
    Note
    ----
    Check that the set of potentially reachable markings does not intersect any feared state. 
   
    Attributes
    ----------
    ptnet : PetriNet
        Initial Petri net.
    formula : Formula
        Reachability formula.
    solver : Z3
        SMT solver (Z3).
    debug : bool
        Debugging flag.
    solver_pids : Queue of int, optional
        Queue to share the current PID.
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, verbose: bool = False, debug: bool = False, solver_pids: Optional[Queue[int]] = None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Formula to study
        self.formula: Formula = formula

        # Verbosity
        self.verbose = verbose

        # SMT solver
        self.solver: Z3 = Z3(debug=debug, solver_pids=solver_pids)
        self.debug: bool = debug
        self.solver_pids: Optional[Queue[int]] = solver_pids

    def prove(self, result: Queue[Verdict], concurrent_pids: Queue[list[int]]):
        """ Prover.

        Parameters
        ----------
        result : Queue of Verdict
            Queue to exchange the verdict.
        concurrent_pids : Queue of int
            Queue to get the PIDs of the concurrent methods.
        """
        set_verbose(self.verbose)

        info("[STATE-EQUATION] RUNNING")

        verdict = self.prove_helper()

        # Kill the solver
        self.solver.kill()
    
        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        if verdict is False:
            result.put(Verdict.NOT_REACHABLE)
        else:
            result.put(Verdict.UNKNOWN)

        # Terminate concurrent methods
        if verdict is False and not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

    ######################
    # TODO: Sect. 2.3.4. #
    ######################
    def prove_helper(self) -> Optional[bool]:
        """
        Determine if the formula is not reachable or potentially reachable.

        Returns
        -------
        bool, optional
            `False` if F is proved as not reachable, `None` otherwise.
        """
        solver = self.solver

        # Declare variables for places and transitions
        solver.write(self.ptnet.smtlib_declare_places())
        solver.write(self.ptnet.smtlib_declare_transition_firing_vector())
        solver.write(self.ptnet.smtlib_set_initial_marking())

        # Generate the state equation
        solver.write(self.ptnet.smtlib_state_equation())

        # Check if F is satisfiable under the state equation constraints
        solver.push()
        solver.write(self.formula.smtlib(assertion=True))
        is_f_sat = solver.check_sat()
        solver.pop()

        if is_f_sat is True:
            # If F is satisfiable, then it is potentially reachable
            return None

        if is_f_sat:
            # We found a solution in the over-approx => cannot conclude not reachable => unknown
            return None
        else:
            # No solution under the incidence constraints. If it's an equality => definitely not reachable
            # Otherwise treat it as unknown, because the method is incomplete
            formula_text = str(self.formula)
            if '=' in formula_text:
                return False
            else:
                return None