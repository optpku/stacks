/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DimensionFormula
import StacksCheckRecall

/-!
# Dimension formula for morphisms of algebraic spaces

A locally finite-type morphism of algebraic spaces with locally Noetherian target
obeys the local dimension formula of Stacks Lemma 67.35.1, comparing local-ring
dimensions and residue-field transcendence degrees at a point against the maximum
transcendence degree at dimension-zero points specializing to that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.exists_isGreatest_residueFieldTrdegAt_specializing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X),
    ∃ E : ℕ, IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E)

/- Lemma 67.35.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian and `f` is
locally of finite type. Let `x` be a point of `|X|` with image
`y = Points.map f x` in `|Y|`. Then
`localRingDimAt x + residueFieldTrdegAt f x ≤ localRingDimAt y + E`,
equivalently the source subtraction form
`localRingDimAt x ≤ localRingDimAt y + E - residueFieldTrdegAt f x`,
where `E` is the maximum of `residueFieldTrdegAt f ξ` over points `ξ` of
`|X|` with `ξ ⤳ x` and `localRingDimAt ξ = 0`, using the canonical topology
on `|X|`. This maximum exists under the stated hypotheses. -/
@[stacks 0BAX] #check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_add_trdeg_le_genericMax :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X) (E : ℕ),
    IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E →
    localRingDimAt x + (residueFieldTrdegAt f x : WithBot ℕ∞) ≤
      localRingDimAt (Points.map f x) + (E : WithBot ℕ∞))

end AlgebraicGeometry.AlgebraicSpace
