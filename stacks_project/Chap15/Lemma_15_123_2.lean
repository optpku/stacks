/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.Perturbation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.123.2

The source perturbation `h : K⁰ → L⁻¹`, both component formulas, and both surjectivity conditions
remain explicit in the ReasLib owner.  The derived admissibility of the perturbed map is a separate
glue theorem, so callers do not have to manufacture an extra admissibility argument.

@stack 0FJK
-/

/- Lemma 15.123.2: a surjective two-term perturbation leaves the determinant map unchanged. -/
@[stacks 0FJK "Lemma 15.123.2: determinant map is invariant under a surjective perturbation"]
#check @CochainComplex.Determinant.equiv_eq_of_perturbation

#check @CochainComplex.Determinant.IsAdmissible.ofPerturbation
#check @CochainComplex.Determinant.equiv
#check @CochainComplex.Determinant.map_eq_of_perturbation
#check @CochainComplex.Determinant.map

end
