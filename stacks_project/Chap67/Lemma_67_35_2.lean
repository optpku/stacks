/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg

/-!
# Global dimension bound for morphisms of algebraic spaces

A locally finite-type morphism of algebraic spaces with locally Noetherian target
obeys the global dimension bound of Stacks Lemma 67.35.2: the dimension of the
source is at most the dimension of the target plus the supremum of residue-field
transcendence degrees at points of local-ring dimension zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The supremum of residue-field transcendence degrees of `f` at points of `|X|`
where the local ring of `X` has dimension `0`. -/
noncomputable def localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : ℕ∞ :=
  ⨆ ξ : Points X, ⨆ _ : localRingDimAt ξ = 0, (residueFieldTrdegAt f ξ : ℕ∞)

/-- The residue-field transcendence degree of `f` at a point of local-ring
dimension `0` is at most `localRingDimZeroTrdeg f`. -/
theorem le_localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {ξ : Points X} (hξ : localRingDimAt ξ = 0) :
    (residueFieldTrdegAt f ξ : ℕ∞) ≤ localRingDimZeroTrdeg f :=
  sorry

/-- Lemma 67.35.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian and `f` is
locally of finite type. Then
`dimension X ≤ dimension Y + localRingDimZeroTrdeg f`,
where `localRingDimZeroTrdeg f` is the supremum of `residueFieldTrdegAt f ξ`
over points `ξ` of `|X|` at which `localRingDimAt ξ = 0`. -/
@[stacks 0BAY]
theorem dimension_le_add_localRingDimZeroTrdeg
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    dimension X ≤ dimension Y + (localRingDimZeroTrdeg f : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
