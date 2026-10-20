/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentInverseImage

/-!
# Inverse image of the cotangent complex along a morphism of topoi

Lemma 92.18.3 identifies `f⁻¹ L(B/A)` with `L(f⁻¹B / f⁻¹A)` for a morphism of topoi
`f : Sh(D) ⟶ Sh(C)` and a homomorphism of sheaves of rings on `C`.
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

/- Lemma 92.18.3. Let `f : Sh(D) ⟶ Sh(C)` be a morphism of topoi. Let `A ⟶ B` be a
homomorphism of sheaves of rings on `C`. Then `f⁻¹ L(B/A) = L(f⁻¹B / f⁻¹A)` as a
canonical isomorphism of complexes of sheaves of modules over `f⁻¹B`. -/
@[stacks 08SV] #check (SheafOfModules.RingedSite.CotangentComplex.InverseImage.iso :
  ∀ (f : CategoryTheory.MorphismOfTopoiIn.{u, u, u, u, u} JC JD)
    {A B : Sheaf JC CommRingCat.{u}} (φ : A ⟶ B),
    SheafOfModules.RingedSite.CotangentComplex.InverseImage.source f φ ≅
      SheafOfModules.RingedSite.CotangentComplex.InverseImage.target f φ)

/- The degree `-n` component of the inverse-image comparison is the standard-resolution map. -/
#check (SheafOfModules.RingedSite.CotangentComplex.InverseImage.iso_hom_f :
  ∀ (f : CategoryTheory.MorphismOfTopoiIn.{u, u, u, u, u} JC JD)
    {A B : Sheaf JC CommRingCat.{u}} (φ : A ⟶ B) (n : ℕ),
    (SheafOfModules.RingedSite.CotangentComplex.InverseImage.iso f φ).hom.f (-n) =
      (SheafOfModules.RingedSite.CotangentComplex.InverseImage.sourceXIso f φ n).hom ≫
        (SheafOfModules.RingedSite.CotangentComplex.InverseImage.termIso f φ n).hom ≫
          (SheafOfModules.RingedSite.CotangentComplex.InverseImage.targetXIso f φ n).inv)

end
end
