/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
import ReasLib.AlgebraicGeometry.ChowGroup.Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.61.1: the exterior product of cycles over a field descends through rational
equivalence in both variables to a degreewise exterior product on Chow groups. -/
@[stacks 0FBV] #check (AlgebraicGeometry.ChowGroup.exteriorProduct :
  {k : Type u} → [Field k] →
    (X Y : AlgebraicGeometry.SchemeOverField k) →
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] →
    (n m : ℤ) →
    TensorProduct ℤ
        (AlgebraicGeometry.RelativeChow (fun _ ↦ 0) X n)
        (AlgebraicGeometry.RelativeChow (fun _ ↦ 0) Y m) →+
      AlgebraicGeometry.RelativeChow (fun _ ↦ 0) (X ⨯ Y) (n + m))
