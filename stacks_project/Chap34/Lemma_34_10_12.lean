/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Sheaf

@[expose] public section

open CategoryTheory

universe u v

/-!
# Lemma 34.10.12

This chapter entry is a compatibility facade for finite affine and singleton
tests of the `V`-sheaf condition.
-/

/- Lemma 34.10.12: A scheme presheaf is a `V`-sheaf exactly when it is a
Zariski sheaf satisfying descent for every finite affine standard `V` cover. -/
@[stacks 0ETM] #check
  (AlgebraicGeometry.satisfiesVSheafProperty_iff_zariski_and_standardV :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.satisfiesVSheafProperty F ↔
        AlgebraicGeometry.satisfiesZariskiSheafProperty F ∧
          AlgebraicGeometry.satisfiesStandardVSheafProperty F)

#check
  (AlgebraicGeometry.satisfiesStandardVSheafProperty_iff_singleton :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v)
      (hzar : AlgebraicGeometry.satisfiesZariskiSheafProperty F),
        AlgebraicGeometry.satisfiesStandardVSheafProperty F ↔
          AlgebraicGeometry.satisfiesStandardVSingletonSheafProperty F)
