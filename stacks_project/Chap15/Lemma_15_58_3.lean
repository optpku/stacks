/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# Lemma 15.58.3

@stack 0GWP

The symmetric monoidal homotopy category and its monoidal quotient functor
are owned by `CategoryTheory.HomotopyCategory.Koszul`.
-/

@[expose] public section

/- Lemma 15.58.3, tag `0GWP`: the homotopy category of cochain complexes is symmetric monoidal
for the totalized tensor product. -/
@[stacks 0GWP]
#check @CategoryTheory.HomotopyCategory.Koszul.symmetricCategory

/- The corresponding canonical monoidal structure. -/
#check @CategoryTheory.HomotopyCategory.Koszul.monoidalCategory

/- The monoidal quotient functor from complexes to the homotopy category. -/
#check @CategoryTheory.HomotopyCategory.Koszul.quotientMonoidal
