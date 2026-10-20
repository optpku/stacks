/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DimensionFormula
import StacksCheckRecall

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

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimZeroTrdeg :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → ℕ∞)

#check (AlgebraicGeometry.AlgebraicSpace.le_localRingDimZeroTrdeg :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {ξ : Points X},
    localRingDimAt ξ = 0 →
      residueFieldTranscendenceDegreeAt f ξ ≤ localRingDimZeroTrdeg f)

/- Lemma 67.35.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian and `f` is
locally of finite type. Then
`dimension X ≤ dimension Y + localRingDimZeroTrdeg f`,
where `localRingDimZeroTrdeg f` is the supremum of `residueFieldTrdegAt f ξ`
over points `ξ` of `|X|` at which `localRingDimAt ξ = 0`. -/
@[stacks 0BAY] #check (AlgebraicGeometry.AlgebraicSpace.dimension_le_add_localRingDimZeroTrdeg :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y],
    dimension X ≤ dimension Y + (localRingDimZeroTrdeg f : WithBot ℕ∞))
