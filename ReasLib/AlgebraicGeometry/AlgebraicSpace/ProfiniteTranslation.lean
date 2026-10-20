module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# A residual-space factorization counterexample

For a field `k` and an infinite profinite group `G`, the translation quotient
`X = Y / Γ` of `Y = Spec(LocallyConstant G k)` is a one-point algebraic space whose
origin `k`-point is a monomorphism, but the projection `q : Y ⟶ X` does not factor
through any `Spec(K) ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Points
open AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

/-- The translation quotient `X = Y / Γ` is a singleton space,
with unique point the origin `k`-point `x`. -/
theorem points_eq_singleton (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    (Set.univ : Set (Points (X k G))) = {Points.mk (x k G)} := sorry

/-- The projection `q : Y ⟶ X` does not factor through any
morphism `Spec(K) ⟶ X` from the spectrum of a field. -/
theorem not_exists_fieldValued_factor (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] :
    ¬ ∃ (p : FieldValuedPoint (X k G)) (φ : ofOver (YOver k G) ⟶ ofOver p.overObj),
        φ ≫ p.hom = q k G := sorry

/-- The pullback of `q` along `x` is the structure morphism
`Γ ⟶ Spec(k)`, with first projection the orbit map. -/
theorem isPullback_orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    IsPullback (ofOverMap (orbit k G)) (ofOverMap (ΓToBase k G)) (q k G) (x k G).hom :=
  sorry

/-- The orbit map `Γ ⟶ Y`, `g ↦ g · 1`, has no section. -/
theorem not_exists_section_orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] :
    ¬ ∃ s : YOver k G ⟶ ΓOver k G, s ≫ orbit k G = 𝟙 (YOver k G) := sorry

/-- The translation quotient is not locally Noetherian. -/
theorem not_isLocallyNoetherian_X (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] : ¬ IsLocallyNoetherian (X k G) := sorry

/-- The translation quotient is not decent. -/
theorem not_isDecent_X (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    ¬ IsDecent (X k G) := sorry

end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
