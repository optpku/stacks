/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.CompleteDevissage.EtaleCover
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 77.4.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite type morphism of
algebraic spaces over `S`. Let `F` be a finite type quasi-coherent `𝒪_X`-module.
Let `y ∈ |Y|` be a point. There exists an étale morphism `(Y', y') → (Y, y)` with
`Y'` an affine scheme and étale morphisms `h_i : W_i → X_{Y'}`, `i = 1, …, n`
such that for each `i` there exists a complete dévissage of `F_i / W_i / Y'` over
`y'`, where `F_i` is the pullback of `F` to `W_i`, and such that
`|(X_{Y'})_{y'}| ⊆ ⋃ h_i(W_i)`. -/
@[stacks 0CWJ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleCoverWithCompleteDevissages :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
      [AlgebraicSpace.FiniteType f] → (F : X.Modules) → [F.IsQuasicoherent] →
        [F.IsFiniteType] → (y : Points Y) →
          ∃ (Y' : smallEtaleSite Y) (y' : Y'.left.left),
            IsAffine Y'.left.left ∧ Points.mapOfOver Y'.hom y' = y ∧
              ∃ (n : ℕ) (W : Fin n → smallEtaleSite (Limits.pullback f Y'.hom))
                (D : ∀ i, Scheme.Modules.CompleteDevissageOver
                  (schemeHomToBase f Y' (W i))
                  (Modules.pullbackToEtaleChart f Y' (W i) F) y'),
                Set.range
                    (Points.map
                      (fieldFiberι (Limits.pullback.snd f Y'.hom)
                        (FieldValuedPoint.ofScheme
                          (Scheme.FieldValuedPoint.residuePoint y')))) ⊆
                  ⋃ i, Set.range (Points.mapOfOver (W i).hom))
