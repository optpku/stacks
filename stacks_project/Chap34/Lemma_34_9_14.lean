/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Sheaf

@[expose] public section

open CategoryTheory

universe u v

/-!
# Lemma 34.9.14

This chapter entry is a compatibility facade for the standard fpqc sheaf
tests.
-/

/- Lemma 34.9.14: the fpqc condition is exposed through standard affine chart
tests and faithfully-flat singleton tests. -/
@[stacks 022H] #check
  (AlgebraicGeometry.satisfiesFpqcSheafProperty_iff_zariski_and_standardFpqc :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.satisfiesFpqcSheafProperty F ↔
        AlgebraicGeometry.satisfiesZariskiSheafProperty F ∧
          AlgebraicGeometry.satisfiesStandardFpqcSheafProperty F)

#check
  (AlgebraicGeometry.satisfiesStandardFpqcSheafProperty_iff_affineFaithfullyFlatSingleton :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v)
      (_ : AlgebraicGeometry.satisfiesZariskiSheafProperty F),
      AlgebraicGeometry.satisfiesStandardFpqcSheafProperty F ↔
        AlgebraicGeometry.satisfiesAffineFaithfullyFlatSingletonSheafProperty F)
