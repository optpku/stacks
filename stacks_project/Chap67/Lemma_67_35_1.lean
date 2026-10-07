module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Dimension formula for morphisms of algebraic spaces

A locally finite-type morphism of algebraic spaces with locally Noetherian target
obeys the local dimension formula of Stacks Lemma 67.35.1, comparing local-ring
dimensions and residue-field transcendence degrees at a point against the maximum
transcendence degree among dimension-zero specializations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.35.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian and `f` is
locally of finite type. Let `x` be a point of `|X|` with image
`y = Points.map f x` in `|Y|`. Then
`localRingDimAt x + residueFieldTrdegAt f x ≤ localRingDimAt y + E`,
equivalently the source subtraction form
`localRingDimAt x ≤ localRingDimAt y + E - residueFieldTrdegAt f x`,
where `E` is the maximum of `residueFieldTrdegAt f ξ` over points `ξ` of
`|X|` with `@Specializes (Points X) τ ξ x` and `localRingDimAt ξ = 0`,
for the canonical topology `τ` on `|X|`. -/
@[stacks 0BAX]
theorem localRingDimAt_add_trdeg_le_genericMax
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (x : Points X) {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (E : ℕ)
    (hE : IsGreatest (setOf fun n ↦ ∃ ξ : Points X,
      @Specializes (Points X) τ ξ x ∧ localRingDimAt ξ = 0 ∧
        n = residueFieldTrdegAt f ξ) E) :
    localRingDimAt x + (residueFieldTrdegAt f x : WithBot ℕ∞) ≤
      localRingDimAt (Points.map f x) + (E : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
