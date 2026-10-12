/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Homology
import StacksCheckRecall

/-!
# Lemma 15.87.3

@stack 0918
-/

@[expose] public section

/-
Lemma 15.87.3 (Stacks 0918): for a sequential inverse system `A` of cochain complexes of
abelian groups, vanishing of the three `R¹ lim` terms in degrees `-2`, `-1`, and `H⁻¹` makes
the canonical comparison `H⁰(lim A) ⟶ lim H⁰(A)` an isomorphism.  The shared theorem is
formulated uniformly in the cohomological degree; specializing `n := 0` recovers the source
statement without introducing a chapter-local alias.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

@[stacks 0918] #check
  CategoryTheory.SequentialInverseSystem.LimitHomology.isIso_of_r1Vanishing (n := 0)

#check @CategoryTheory.SequentialInverseSystem.LimitHomology.shortExact_of_r1Vanishing
#check @CategoryTheory.SequentialInverseSystem.LimitHomology.isIso_of_mittagLeffler
