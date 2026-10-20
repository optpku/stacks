/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentInverseImage

/-!
# Inverse-image cotangent-complex compatibility bridge

This source-side module keeps a lightweight import path for consumers of the inverse-image
cotangent-complex API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/- The commutative-ring inverse-image functor is available to source-side consumers. -/
#check (CategoryTheory.MorphismOfTopoiIn.commRingInverseImage :
  ∀ (f : CategoryTheory.MorphismOfTopoiIn.{u, u, u, u, u} JC JD),
    Sheaf JC CommRingCat.{u} ⥤ Sheaf JD CommRingCat.{u})

/- The inverse-image cotangent-complex comparison is available to source-side consumers. -/
#check (SheafOfModules.RingedSite.CotangentComplex.InverseImage.iso :
  ∀ (f : CategoryTheory.MorphismOfTopoiIn.{u, u, u, u, u} JC JD)
    {A B : Sheaf JC CommRingCat.{u}} (φ : A ⟶ B),
    SheafOfModules.RingedSite.CotangentComplex.InverseImage.source f φ ≅
      SheafOfModules.RingedSite.CotangentComplex.InverseImage.target f φ)

end
end
