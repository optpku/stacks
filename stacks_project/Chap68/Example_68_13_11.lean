module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_11_Factorization
public import stacks_project.Chap68.Example_68_13_11_Presentation
public import stacks_project.Chap68.Example_68_13_11_Space
public import stacks_project.Chap68.Lemma_68_12_8_Decent

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

/-- Example 68.13.11 (1): the affine scheme `Y = Spec(LocallyConstant G k)` is affine. -/
@[stacks 0H2Y]
theorem isAffine_Y (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    AlgebraicGeometry.IsAffine (YOver k G).left := sorry

/-- Example 68.13.11 (2): the affine scheme `Y = Spec(LocallyConstant G k)` is reduced. -/
@[stacks 0H2Y]
theorem isReduced_Y (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    AlgebraicGeometry.IsReduced (YOver k G).left := sorry

/-- Example 68.13.11 (3): the translation quotient `X = Y / Γ` is a singleton space,
with unique point the origin `k`-point `x`. -/
@[stacks 0H2Y]
theorem points_eq_singleton (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    (Set.univ : Set (Points (X k G))) = {Points.mk (x k G)} := sorry

/-- Example 68.13.11 (4): the origin `k`-point `x : Spec(k) ⟶ X` is a split monomorphism,
as a section of `X ⟶ Spec(k)`. -/
@[stacks 0H2Y]
theorem isSplitMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    IsSplitMono (x k G).hom := sorry

/-- Example 68.13.11 (5): the projection `q : Y ⟶ X` does not factor through any
morphism `Spec(K) ⟶ X` from the spectrum of a field. -/
@[stacks 0H2Y]
theorem not_exists_fieldValued_factor (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] :
    ¬ ∃ (p : FieldValuedPoint (X k G)) (φ : ofOver (YOver k G) ⟶ ofOver p.overObj),
        φ ≫ p.hom = q k G := sorry

/-- Example 68.13.11 (6): the pullback of `q` along `x` is the structure morphism
`Γ ⟶ Spec(k)`, with first projection the orbit map. -/
@[stacks 0H2Y]
theorem isPullback_orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    IsPullback (ofOverMap (orbit k G)) (ofOverMap (ΓToBase k G)) (q k G) (x k G).hom :=
  sorry

/-- Example 68.13.11 (7): the orbit map `Γ ⟶ Y`, `g ↦ g · 1`, has no section. -/
@[stacks 0H2Y]
theorem not_exists_section_orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] :
    ¬ ∃ s : YOver k G ⟶ ΓOver k G, s ≫ orbit k G = 𝟙 (YOver k G) := sorry

/-- The origin `k`-point is a monomorphism. -/
instance instMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Mono (x k G).hom :=
  sorry

/-- The image of `q` on points is the singleton `{x}`. -/
theorem range_q_eq_singleton (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    Set.range (Points.map (q k G)) = {Points.mk (x k G)} := sorry

/-- Any field-valued factorization of `q` factors through the monomorphism `x`, by
Properties of Spaces, Lemma 66.4.11. -/
theorem factors_through_x_of_fieldValued (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] (p : FieldValuedPoint (X k G))
    (φ : ofOver (YOver k G) ⟶ ofOver p.overObj) (hφ : φ ≫ p.hom = q k G) :
    Nonempty (p.Factorization (x k G)) := sorry

/-- The translation quotient is not locally Noetherian. -/
theorem not_isLocallyNoetherian_X (k : Type u) [Field k] (G : ProfiniteGrp.{u})
    [Infinite G] : ¬ IsLocallyNoetherian (X k G) := sorry

/-- The translation quotient is not decent. -/
theorem not_isDecent_X (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G] :
    ¬ IsDecent (X k G) := sorry

end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
