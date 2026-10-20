/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AdequatePresheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- 46.7.3.1: For an affine scheme `U = Spec A`, the inclusion of adequate
`𝒪`-modules into module presheaves on `(Aff / U)_τ` is the composite of the
full-subcategory inclusion into module sheaves with the canonical forgetful functor. -/
@[stacks 06ZT]
#check (SheafOfModules.Adeq.toPresheaf :
  (A : CommRingCat.{u}) →
    (τ : StandardTopology) →
    (underline : (B : CommRingCat.{u}) →
      ModuleCat.{u} B ⥤ (Under B ⥤ AddCommGrpCat.{u})) →
    (affineEvaluation :
      RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) →
        (B : CommRingCat.{u}) →
          (Scheme.Spec.obj (op B) ⟶ Scheme.Spec.obj (op A)) →
            Under B ⥤ AddCommGrpCat.{u}) →
      SheafOfModules.Adeq (S := Scheme.Spec.obj (op A)) (τ := τ)
          underline affineEvaluation ⥤
        _root_.PresheafOfModules.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))).structureSheaf.obj)
