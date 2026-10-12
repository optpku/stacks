/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace WeilCohomology.HodgeRegrading

/-- The Hodge bidegree `(p, q)` has regraded degree `3 * p - q`. -/
def weight (pq : ℤ × ℤ) : ℤ :=
  3 * pq.1 - pq.2

/-- The Hodge regrading weight is additive. -/
theorem weight_add (a b : ℤ × ℤ) :
    weight (a + b) = weight a + weight b := sorry

/-- The Hodge regrading preserves the parity of the usual total degree. -/
theorem weight_mod_two (pq : ℤ × ℤ) :
    weight pq % 2 = (pq.1 + pq.2) % 2 := sorry

/-- Regrade a Hodge-bigraded complex realization by the weight `(p, q) ↦ 3 * p - q`. -/
noncomputable def realization
    (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ)) :
    ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject ℤ (ModuleCat ℂ) :=
  G₂ ⋙ GradedObject.map (ModuleCat ℂ) weight

/-- Degree `n` of the regraded realization is the coproduct of the Hodge components
whose weight is `n`. -/
theorem realization_obj
    (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ))
    (M : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ)) :
    (realization G₂).obj M = (G₂.obj M).mapObj weight := sorry

/-- Regrading by `weight` is ℚ-linear on morphisms. -/
noncomputable instance weightMapLinear :
    (GradedObject.map (ModuleCat ℂ) weight).Linear ℚ := sorry

/-- If every Hodge bidegree of the Tate twist `𝟙(1)` with weight other than `-2`
is zero, then the regraded realization of that Tate twist vanishes off degree `-2`. -/
theorem tateTwist_degree
    (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ))
    (h_support : ∀ pq : ℤ × ℤ,
      weight pq ≠ -2 →
        IsZero ((G₂.obj (ChowMotive.tateTwist (SchemeOverField.point ℂ) 1)) pq)) :
    ∀ i : ℤ, i ≠ -2 →
      IsZero (((realization G₂).obj
        (ChowMotive.tateTwist (SchemeOverField.point ℂ) 1)) i) := sorry

/-- If the only Hodge summand of weight `-1` is the one-dimensional `(0, 1)`
summand, then the regraded degree `-1` has dimension one. -/
theorem ellipticFinrankNegOne
    (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ))
    [G₂.Linear ℚ]
    (E : SchemeOverField ℂ) [Variety E] [Smooth E.hom] [Projective E.hom]
    (h_support : ∀ pq : ℤ × ℤ, weight pq = -1 → pq ≠ (0, 1) →
      IsZero ((G₂.obj (ChowMotive.h E)) pq))
    (h_hodge : Module.finrank ℂ ((G₂.obj (ChowMotive.h E)) (0, 1)) = 1) :
    Module.finrank ℂ (((realization G₂).obj (ChowMotive.h E)) (-1)) = 1 := sorry

/-- A one-dimensional degree `-1` component on a smooth projective curve
contradicts the cohomological range-vanishing axiom. -/
theorem notRangeVanishing
    (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ))
    [G₂.Linear ℚ]
    (E : SchemeOverField ℂ) [Variety E] [Smooth E.hom] [Projective E.hom]
    (h_dim : topologicalKrullDim E.left = (1 : WithBot ℕ∞))
    (h_neg : Module.finrank ℂ
      (((realization G₂).obj (ChowMotive.h E)) (-1)) = 1) :
    ¬ ∀ (X : SchemeOverField ℂ) [Variety X] [Smooth X.hom] [Projective X.hom]
        (d : ℕ), topologicalKrullDim X.left = (d : WithBot ℕ∞) →
          ∀ i : ℤ, i < 0 ∨ 2 * (d : ℤ) < i →
            IsZero (((realization G₂).obj (ChowMotive.h X)) i) := sorry

end WeilCohomology.HodgeRegrading
