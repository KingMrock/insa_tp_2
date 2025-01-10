"""
Petri Net Module

Input file format: .net
Standard: http://projects.laas.fr/tina//manuals/formats.html

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

from re import split
from sys import exit
from typing import Optional

MULTIPLIER_TO_INT = {
    'K': 1000,
    'M': 1000000,
    'G': 1000000000,
    'T': 1000000000000,
    'P': 1000000000000000,
    'E': 1000000000000000000
}

pl_id         = str
tr_id         = str
arc_weight    = int
number_tokens = int

class PetriNet:
    """ Petri net.

    Attributes
    ----------

    places : set of str
        Finite set of places (identified by names).
    
    transitions : set of str
        Finite set of transitions (identified by names).

    pre : dict of str: dict of str: int
        Pre-condition function.
    
        self.pre[tr] is defined for all transitions t in self.transitions.
        self.pre[tr][pl] is only defined if there is some arc from pl to tr,
                         in which case the value is the weight.

    post : dict of str: dict of str: int
        Post-condition function.
        
        self.post[tr] is defined for all transitions t in self.transitions.
        self.post[tr][pl] is only defined if there is some arc from tr to pl,
                          in which case the value is the weight.
    
    initial_marking : dict of str: int
        Initial marking.

        self.initial_marking[pl] is defined for all place in self.places.
    """

    def __init__(self, filename: str) -> None:
        """ Initializer.

        Parameters
        ----------
        filename : str
            Petri net filename.
        """
        self.places:          set[pl_id] = set()
        self.transitions:     set[tr_id] = set()
        
        self.pre:             dict[tr_id, dict[pl_id, arc_weight]] = {}
        self.post:            dict[tr_id, dict[pl_id, arc_weight]] = {}
        
        self.initial_marking: dict[pl_id, number_tokens] = {}

        # Parse the `.net` file
        self.parse_net(filename)

    def __str__(self) -> str:
        """ Petri net to .net format.

        Returns
        -------
        str
            .net format.
        """
        text = ""

        for tr in self.transitions:
            text += "tr {}".format(tr)
            
            for pl, weight in self.pre[tr].items():
                if weight != 1:
                    text += " {}*{}".format(weight, pl)
                else:
                    text += " {}".format(pl)

            text += " ->"

            for pl, weight in self.post[tr].items():
                if weight != 1:
                    text += " {}*{}".format(weight, pl)
                else:
                    text += " {}".format(pl)
        
            text += "\n"


        for pl, marking in self.initial_marking.items():
            text += "pl {} ({})\n".format(pl, marking)

        return text

    def smtlib_declare_places(self, k: Optional[int] = None) -> str:
        """ Declare variables corresponding to the number of tokens
            contained into the different places at iteration k.

        Parameters
        ----------
        k : int, optional
            Iteration.

        Returns
        -------
        str
            SMT-LIB format.
        """

        smt_input = ""
        
        for pl in self.places:
            var = pl if k is None else "{}@{}".format(pl, k)
            smt_input += "(declare-const {} Int)\n".format(var)
            smt_input += "(assert (>= {} 0))\n".format(var)

        return smt_input
    
    def smtlib_declare_places_sat(self, k: Optional[int] = None) -> str:
        """
        Declare Boolean variables for places (safe net).
        """
        smt_input = ""
        for pl in self.places:
            var = pl if k is None else f"{pl}@{k}"
            smt_input += f"(declare-const {var} Bool)\n"
        return smt_input

    ######################
    # TODO: Sect. 2.3.1. #
    ######################
    def smtlib_set_initial_marking(self, k: Optional[int] = None) -> str:
        """ Set the initial marking.
        
        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""
        for pl, marking in self.initial_marking.items():
            var = pl if k is None else "{}@{}".format(pl, k)
            smt_input += "(assert (= {} {}))\n".format(var, marking)
        return smt_input
    ######################

    def smtlib_set_initial_marking_sat(self, k: Optional[int] = None) -> str:
        """
        Set initial marking (true = 1 token, false = 0 token) for a safe net.
        """
        smt_input = ""
        for pl, marking in self.initial_marking.items():
            var = pl if k is None else f"{pl}@{k}"
            if marking > 1:
                # Not valid for a safe net; you could raise an error or handle differently.
                smt_input += f"(assert false) ; // Invalid marking > 1 in a safe net\n"
            elif marking == 1:
                smt_input += f"(assert {var})\n"
            else:
                smt_input += f"(assert (not {var}))\n"
        return smt_input

    ######################
    # TODO: Sect. 2.3.1. #
    ######################
    def smtlib_transition_relation(self, k: int, k_prime: int) -> str:
        """ Transition relation from places at iteration k to iteration k + 1.
        
        Parameters
        ----------
        k : int
            Iteration.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = "(assert (or\n"
        for t in self.transitions:
            smt_input += "  (and\n"
            # Enabling condition
            for p in self.pre[t]:
                smt_input += f"    (>= {p}@{k} {self.pre[t][p]})\n"
            # Marking update
            for p in self.places:
                pre_val = self.pre[t].get(p, 0)
                post_val = self.post[t].get(p, 0)
                diff = post_val - pre_val
                if diff == 0:
                    smt_input += f"    (= {p}@{k_prime} {p}@{k})\n"
                else:
                    smt_input += f"    (= {p}@{k_prime} (+ {p}@{k} {diff}))\n"
            smt_input += "  )\n"
        smt_input += "))\n"
        return smt_input
    ######################

    def smtlib_transition_relation_sat(self, k: int, k_prime: int) -> str:
        """
        Transition relation for a safe net:
        each transition can flip the relevant place bits.
        """
        smt_input = "(assert (or\n"
        for t in self.transitions:
            # Building an AND block for firing t at step k => new marking at step k+1
            smt_input += "  (and\n"
            # Pre-condition: all input places must be true
            for p_in, w in self.pre[t].items():
                # For a safe net, w > 1 not allowed, but just in case check w
                if w >= 1:
                    smt_input += f"    {p_in}@{k}\n"
            # Post-condition: all output places become true
            # Input places become false (since only 0/1 token)
            for p in self.pre[t]:
                smt_input += f"    (not {p}@{k_prime})\n"
            for p_out, w in self.post[t].items():
                if w >= 1:
                    smt_input += f"    {p_out}@{k_prime}\n"
            # Other places unchanged
            for p in self.places - set(self.pre[t]) - set(self.post[t]):
                smt_input += f"    (= {p}@{k} {p}@{k_prime})\n"
            smt_input += "  )\n"
        # Also allow 'no transition fires' to keep marking unchanged
        smt_input += "  (and\n"
        for p in self.places:
            smt_input += f"    (= {p}@{k} {p}@{k_prime})\n"
        smt_input += "  )\n"
        smt_input += "))\n"
        return smt_input


    def parse_net(self, filename: str) -> None:
        """ Petri net parser.

        Parameters
        ----------
        filename : str
            Petri net filename (.net format).

        Raises
        ------
        FileNotFoundError
            Petri net file not found.
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():

                    # '#' and ',' forbidden in SMT-LIB
                    content = split(r'\s+', line.strip().replace('#', '.').replace(',', '.'))

                    # Skip empty lines and get the first identifier
                    if not content:
                        continue
                    else:
                        element = content.pop(0)

                    # Transition arcs
                    if element == "tr":
                        self.parse_transition(content)

                    # Place
                    if element == "pl":
                        self.parse_place(content)
            fp.close()
        except FileNotFoundError as e:
            exit("Error: Input file not found")

    def smtlib_declare_transition_firing_vector(self) -> str:
        """ Declare variables for the transition firing vector (z).

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""
        for tr in self.transitions:
            smt_input += f"(declare-const {tr}_f Int)\n"
            smt_input += f"(assert (>= {tr}_f 0))\n"  # Non-negative firing counts
        return smt_input
    
    def smtlib_state_equation(self) -> str:
        """Generate the state equation I·z + m0 = m.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = "(assert (and\n"
        for place in self.places:
            equation = f"(= {place} (+ {self.initial_marking[place]}"
            for transition in self.transitions:
                post_val = self.post[transition].get(place, 0)
                pre_val = self.pre[transition].get(place, 0)
                coeff = post_val - pre_val
                if coeff != 0:
                    equation += f" (* {coeff} {transition}_f)"
            equation += "))\n"
            smt_input += equation
        smt_input += "))\n"
        return smt_input




    def parse_transition(self, content: list[str]) -> None:
        """ Transition parser.

        Parameters
        ----------
        content : list of string
            Content to parse (.net format).
        """
        transition_id = content.pop(0)

        self.transitions.add(transition_id)
        self.pre[transition_id] = {}
        self.post[transition_id] = {}

        content = self.parse_label(content)

        arrow = content.index("->")
        inputs = content[0:arrow]
        outputs = content[arrow + 1:]

        for arc in inputs:
            self.parse_arc(arc, transition_id, self.pre)

        for arc in outputs:
            self.parse_arc(arc, transition_id, self.post)

    def parse_arc(self, content: str, transition_id: str, arcs: dict[tr_id, dict[pl_id, int]]) -> None:
        """ Arc parser.

        Parameters
        ----------
        content : list of str
            Content to parse (.net format).
        transition : str
            Transition that is parsed.
        arcs : dict of str: dict of str: int
            Pre or Post vectors (if parsing before or after ->).
        """
        content = content

        if '*' in content:
            place_id, _, weight_str = content.partition('*')
            weight = self.parse_value(weight_str)
        else:
            place_id = content
            weight = 1

        if place_id not in self.places:
            self.places.add(place_id)
            self.initial_marking[place_id] = 0

        arcs[transition_id][place_id] = arcs[transition_id].get(place_id, 0) + weight

    def parse_place(self, content: list[str]) -> None:
        """ Place parser.

        Parameters
        ----------
        content : list of str
            Place to parse (.net format).
        """
        place_id = content.pop(0)

        content = self.parse_label(content)

        if content:
            initial_marking = self.parse_value(content[0].replace('(', '').replace(')', ''))
        else:
            initial_marking = 0

        if place_id not in self.places:
            self.places.add(place_id)

        self.initial_marking[place_id] = initial_marking

    def parse_label(self, content: list[str]) -> list[str]:
        """ Label parser.

        Parameters
        ----------
        content : list of str
            Content to parse (.net format).

        Returns
        -------
        list of str
            Content without labels.

        """
        index = 0
        if content and content[index] == ':':
            label_skipped = content[index + 1][0] != '{'
            index = 2
            while not label_skipped:
                label_skipped = content[index][-1] == '}'
                index += 1
        return content[index:]

    def parse_value(self, content: str) -> int:
        """ Parse integer value.

        Parameters
        ----------
        content : str
            Content to parse (.net format).

        Returns
        -------
        int
            Corresponding integer value.

        Raises
        ------
        ValueError
            Incorrect integer value.

        """
        if content.isnumeric():
            return int(content)

        multiplier = content[-1]

        if multiplier not in MULTIPLIER_TO_INT:
            raise ValueError("Incorrect integer value")

        return int(content[:-1]) * MULTIPLIER_TO_INT[multiplier]
