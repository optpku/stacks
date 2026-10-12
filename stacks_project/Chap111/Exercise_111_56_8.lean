/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import stacks_project.Chap111.Situation_111_56_5_Notation_plane_curve_Normalization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exercise 111.56.8

An explicit irreducible homogeneous form of degree `100` whose associated
abstract curve has genus `0`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ProjectiveSpace.PlaneCurve

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- Exercise 111.56.8 (1): the homogeneous form `X 1 ^ 100 - X 0 ^ 99 * X 2` of
degree `100` in `k[X 0, X 1, X 2]`, as in Situation 111.56.5. -/
@[stacks 09U3]
def rationalForm (k : Type u) [CommRing k] : MvPolynomial (Fin 3) k :=
  X 1 ^ 100 - X 0 ^ 99 * X 2

/-- Unfolding of `rationalForm k` as `X 1 ^ 100 - X 0 ^ 99 * X 2`. -/
theorem rationalForm_eq (k : Type u) [CommRing k] :
    rationalForm k = X 1 ^ 100 - X 0 ^ 99 * X 2 := sorry

/-- `rationalForm k` lies in the degree-`100` piece of the standard grading on
`k[X 0, X 1, X 2]`. -/
theorem rationalForm_mem_grading (k : Type u) [CommRing k] :
    rationalForm k ∈ ProjectiveSpace.grading k 2 100 := sorry

/-- `rationalForm k` is a nonzero polynomial over a nontrivial ring. -/
theorem rationalForm_ne_zero (k : Type u) [CommRing k] [Nontrivial k] :
    rationalForm k ≠ 0 := sorry

/-- `rationalForm k` is irreducible over a field. -/
theorem irreducible_rationalForm (k : Type u) [Field k] :
    Irreducible (rationalForm k) := sorry

/-- Irreducibility of `rationalForm k`, as a `Fact`. -/
instance instFact_irreducible_rationalForm (k : Type u) [Field k] :
    Fact (Irreducible (rationalForm k)) :=
  ⟨irreducible_rationalForm k⟩

/-- The abstract curve attached to `rationalForm k` in Situation 111.56.5 with
`d = 100`. -/
abbrev rationalAbstractCurve (k : Type u) [Field k] : SchemeOverField k :=
  abstractCurve 100 (rationalForm k) (rationalForm_mem_grading k)

/-- The abstract curve attached to `rationalForm k` is projective over `k`. -/
instance instProjective_rationalAbstractCurve (k : Type u) [Field k] :
    Projective (rationalAbstractCurve k).hom := sorry

/-- The abstract curve attached to `rationalForm k` is smooth over `k`. -/
instance instSmooth_rationalAbstractCurve (k : Type u) [Field k] :
    Smooth (rationalAbstractCurve k).hom := sorry

/-- The abstract curve attached to `rationalForm k` is geometrically irreducible
over `k`. -/
instance instGeometricallyIrreducible_rationalAbstractCurve (k : Type u) [Field k] :
    GeometricallyIrreducible (rationalAbstractCurve k).hom := sorry

/-- Exercise 111.56.8 (2): the abstract curve `C` attached to `rationalForm k`
in Situation 111.56.5 with `d = 100` has genus `0`. -/
@[stacks 09U3]
theorem genus_eq_zero (k : Type u) [Field k] [IsAlgClosed k] :
    Curve.genus (rationalAbstractCurve k) = 0 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
