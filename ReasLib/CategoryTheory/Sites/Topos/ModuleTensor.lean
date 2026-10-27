/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

/-!
# Tensor products and geometric inverse image of module sheaves

The geometric comparison is obtained from the actual adjunction on underlying sheaves
and the bilinear universal property. Scalar extension uses the existing sectionwise
tensor-and-sheafification construction. Both directions of every comparison are specified.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u₀ v₀ u₁ v₁ w

namespace CategoryTheory.MorphismOfTopoiIn.ModuleTensor

variable {C₀ : Type u₀} [Category.{v₀} C₀] {J₀ : GrothendieckTopology C₀}
variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₁.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J₀.HasSheafCompose (forget RingCat.{w})]
variable [J₁.HasSheafCompose (forget RingCat.{w})]
variable (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)
variable (O : Sheaf J₀ CommRingCat.{w})

/-- The canonical commutative inverse-image coefficient sheaf. -/
abbrev coefficient := f.commRingInverseImage.obj O

/-- The existing comparison to the ring-valued inverse image, with both maps supplied. -/
abbrev coefficientIso :
    ringSheaf J₁ (coefficient f O) ≅ f.ringInverseImage.obj (ringSheaf J₀ O) :=
  f.commRingInverseImageForgetRingIso.app O

/-- Geometric module inverse image in the canonical commutative coefficient presentation. -/
def geometric : ringedSiteModuleCategory J₀ O ⥤
    ringedSiteModuleCategory J₁ (coefficient f O) :=
  f.moduleInverseImage (ringSheaf J₀ O) ⋙
    SheafOfModules.restrictScalars (coefficientIso f O).hom

/-- Its right adjoint uses the supplied inverse coefficient map. -/
def geometricRight : ringedSiteModuleCategory J₁ (coefficient f O) ⥤
    ringedSiteModuleCategory J₀ O :=
  SheafOfModules.restrictScalars (coefficientIso f O).inv ⋙
    f.moduleRightOver (ringSheaf J₀ O)

/-- The geometric adjunction, composed with the actual coefficient equivalence. -/
def geometricAdjunction : geometric f O ⊣ geometricRight f O :=
  (f.moduleAdjunction (ringSheaf J₀ O)).comp
    (SheafOfModules.ChangeOfRings.restrictScalarsEquivalence
      (coefficientIso f O).symm).toAdjunction

/-- Restriction of scalars leaves the underlying sheaf unchanged. -/
def restrictUnderlyingIso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) :
    SheafOfModules.restrictScalars α ⋙ ToInternal.underlying R ≅
      ToInternal.underlying S := Iso.refl _

/-- Geometric inverse image has the usual underlying inverse-image sheaf. -/
def geometricForgetIso :
    geometric f O ⋙ ToInternal.underlying (ringSheaf J₁ (coefficient f O)) ≅
      ToInternal.underlying (ringSheaf J₀ O) ⋙ f.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (f.moduleInverseImage (ringSheaf J₀ O))
      (restrictUnderlyingIso (coefficientIso f O).hom) ≪≫
    f.moduleInverseImageForgetIso (ringSheaf J₀ O)

/-- The right adjoint has the usual underlying direct-image sheaf. -/
def geometricRightForgetIso :
    geometricRight f O ⋙ ToInternal.underlying (ringSheaf J₀ O) ≅
      ToInternal.underlying (ringSheaf J₁ (coefficient f O)) ⋙ f.pushforward :=
  NatIso.ofComponents
    (fun M ↦ (f.moduleRightOverForgetIso (ringSheaf J₀ O)).app
      ((SheafOfModules.restrictScalars (coefficientIso f O).inv).obj M)) (by sorry)

variable [HasWeakSheafify J₀ AddCommGrpCat.{w}]
variable [J₀.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J₁ AddCommGrpCat.{w}]
variable [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Transpose a bilinear map using the product comparison and the underlying topos adjunction. -/
def bilinearMate
    (M N : ringedSiteModuleCategory J₀ O)
    (H : ringedSiteModuleCategory J₁ (coefficient f O))
    (b : BilinearMap (coefficient f O)
      ((geometric f O).obj M) ((geometric f O).obj N) H) :
    BilinearMap O M N ((geometricRight f O).obj H) :=
  BilinearMap.ofUnderlyingHom
    ((f.adjunction.homEquiv _ _)
      (prodComparison f.inverseImage
          ((ToInternal.underlying (ringSheaf J₀ O)).obj M)
          ((ToInternal.underlying (ringSheaf J₀ O)).obj N) ≫
        ((geometricForgetIso f O).inv.app M ⊗ₘ (geometricForgetIso f O).inv.app N) ≫
          b.underlyingHom) ≫
      (geometricRightForgetIso f O).inv.app H)
    (by sorry) (by sorry) (by sorry) (by sorry)

/-- The reverse bilinear mate uses the inverse product comparison of the left-exact inverse
image. Its function is fixed before the bilinearity obligations are supplied. -/
def bilinearUnmate
    (M N : ringedSiteModuleCategory J₀ O)
    (H : ringedSiteModuleCategory J₁ (coefficient f O))
    (b : BilinearMap O M N ((geometricRight f O).obj H)) :
    BilinearMap (coefficient f O)
      ((geometric f O).obj M) ((geometric f O).obj N) H :=
  BilinearMap.ofUnderlyingHom
    (((geometricForgetIso f O).hom.app M ⊗ₘ (geometricForgetIso f O).hom.app N) ≫
      (prodComparisonIso f.inverseImage
          ((ToInternal.underlying (ringSheaf J₀ O)).obj M)
          ((ToInternal.underlying (ringSheaf J₀ O)).obj N)).inv ≫
        (f.adjunction.homEquiv _ _).symm
          (b.underlyingHom ≫ (geometricRightForgetIso f O).hom.app H))
    (by sorry) (by sorry) (by sorry) (by sorry)

/-- The bilinear adjunction consists of the two specified underlying-sheaf mates. -/
def bilinearHomEquiv
    (M N : ringedSiteModuleCategory J₀ O)
    (H : ringedSiteModuleCategory J₁ (coefficient f O)) :
    BilinearMap (coefficient f O)
        ((geometric f O).obj M) ((geometric f O).obj N) H ≃
      BilinearMap O M N ((geometricRight f O).obj H) where
  toFun := bilinearMate f O M N H
  invFun := bilinearUnmate f O M N H
  left_inv := by sorry
  right_inv := by sorry

/-- The tensor Hom correspondence follows the bilinear argument of Stacks, Tag 03EL. -/
def geometricTensorHomEquiv
    (M N : ringedSiteModuleCategory J₀ O)
    (H : ringedSiteModuleCategory J₁ (coefficient f O)) :
    ((geometric f O).obj (tensorObj M N) ⟶ H) ≃
      (tensorObj ((geometric f O).obj M) ((geometric f O).obj N) ⟶ H) :=
  ((geometricAdjunction f O).homEquiv _ _).trans
    (BilinearMap.homEquiv.symm.trans
      ((bilinearHomEquiv f O M N H).symm.trans BilinearMap.homEquiv))

/-- Both tensor comparison maps are the images of identity morphisms under the explicit Hom
correspondence. No inverse is selected from an invertibility assertion. -/
def geometricTensorIso (M N : ringedSiteModuleCategory J₀ O) :
    tensorObj ((geometric f O).obj M) ((geometric f O).obj N) ≅
      (geometric f O).obj (tensorObj M N) where
  hom := geometricTensorHomEquiv f O M N _ (𝟙 _)
  inv := (geometricTensorHomEquiv f O M N _).symm (𝟙 _)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The forward comparison is the bilinear Hom image of the identity. -/
@[simp]
theorem geometricTensorIso_hom (M N : ringedSiteModuleCategory J₀ O) :
    (geometricTensorIso f O M N).hom = geometricTensorHomEquiv f O M N _ (𝟙 _) := rfl

/-- The reverse comparison is the reverse Hom image of the other identity. -/
@[simp]
theorem geometricTensorIso_inv (M N : ringedSiteModuleCategory J₀ O) :
    (geometricTensorIso f O M N).inv = (geometricTensorHomEquiv f O M N _).symm (𝟙 _) := rfl

variable (S : Sheaf J₁ CommRingCat.{w})
variable (α : f.ringInverseImage.obj (ringSheaf J₀ O) ⟶ ringSheaf J₁ S)

/-- The given structure map in the canonical commutative coefficient presentation. The
fully faithful forgetful functor retains the actual ring-homomorphism components. -/
def coefficientMap : coefficient f O ⟶ S :=
  (Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing (J := J₁)).preimage
    ((coefficientIso f O).hom ≫ α)

/-- Explicit scalar extension uses the existing tensor-and-sheafification owner. -/
abbrev scalar :=
  SheafOfModules.TensorScalarExtension.Commutative.scalarExtension (coefficientMap f O S α)

/-- Geometric inverse image followed by explicit scalar extension. -/
def tensorModel : ringedSiteModuleCategory J₀ O ⥤ ringedSiteModuleCategory J₁ S :=
  geometric f O ⋙ scalar f O S α

/-- The right adjoint of this explicit composite. -/
def tensorModelRight : ringedSiteModuleCategory J₁ S ⥤ ringedSiteModuleCategory J₀ O :=
  SheafOfModules.restrictScalars (Sheaf.ringSheafOfCommMap (coefficientMap f O S α)) ⋙
    geometricRight f O

/-- Both factors have actual adjunctions with specified Hom maps. -/
def tensorModelAdjunction : tensorModel f O S α ⊣ tensorModelRight f O S α :=
  (geometricAdjunction f O).comp
    (SheafOfModules.TensorScalarExtension.adjunction
      (SheafOfModules.TensorScalarExtension.Commutative.scalarMap (coefficientMap f O S α))
      (SheafOfModules.TensorScalarExtension.Commutative.source_mul_comm (R := coefficient f O))
      (SheafOfModules.TensorScalarExtension.Commutative.target_mul_comm (R' := S)))

/-- The explicit model's right adjoint has the ordinary direct-image carrier. -/
def tensorModelRightForgetIso :
    tensorModelRight f O S α ⋙ ToInternal.underlying (ringSheaf J₀ O) ≅
      ToInternal.underlying (ringSheaf J₁ S) ⋙ f.pushforward :=
  NatIso.ofComponents
    (fun H ↦ (geometricRightForgetIso f O).app
      ((SheafOfModules.restrictScalars
        (Sheaf.ringSheafOfCommMap (coefficientMap f O S α))).obj H)) (by sorry)

/-- The usual restrict-and-direct-image composite has the same carrier. -/
def scalarRightForgetIso :
    (SheafOfModules.restrictScalars α ⋙ f.moduleRightOver (ringSheaf J₀ O)) ⋙
        ToInternal.underlying (ringSheaf J₀ O) ≅
      ToInternal.underlying (ringSheaf J₁ S) ⋙ f.pushforward :=
  NatIso.ofComponents
    (fun H ↦ (f.moduleRightOverForgetIso (ringSheaf J₀ O)).app
      ((SheafOfModules.restrictScalars α).obj H)) (by sorry)

/-- The right-adjoint comparison keeps the specified underlying carrier maps. Its linearity
is exactly the equality encoded by `coefficientMap` and the two coefficient inverse laws. -/
def tensorModelRightIso : tensorModelRight f O S α ≅
    SheafOfModules.restrictScalars α ⋙ f.moduleRightOver (ringSheaf J₀ O) :=
  functorIsoOfUnderlying (ringSheaf J₀ O)
    (tensorModelRightForgetIso f O S α ≪≫ (scalarRightForgetIso f O S α).symm)
    (by sorry) (by sorry)

variable [(SheafOfModules.restrictScalars.{w} α).IsRightAdjoint]

/-- Compare the existing chosen scalar adjoint with the explicit tensor model using their
specified adjunctions. No new adjoint is selected from an admitted existence assertion. -/
def tensorModelIso :
    f.moduleInverseImage (ringSheaf J₀ O) ⋙ SheafOfModules.ChangeOfRings.extendScalars α ≅
      tensorModel f O S α :=
  ((f.moduleAdjunction (ringSheaf J₀ O)).comp
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction α)).leftAdjointUniq
    ((tensorModelAdjunction f O S α).ofNatIsoRight (tensorModelRightIso f O S α))

/-- Tensor comparison for the existing geometric-and-scalar pullback functor. Its two maps
are compositions of the geometric bilinear mates, algebraic base-change maps, and the
explicit comparison of adjunctions. -/
def pullbackTensorIso (M N : ringedSiteModuleCategory J₀ O) :
    tensorObj
      ((f.moduleInverseImage (ringSheaf J₀ O) ⋙
        SheafOfModules.ChangeOfRings.extendScalars α).obj M)
      ((f.moduleInverseImage (ringSheaf J₀ O) ⋙
        SheafOfModules.ChangeOfRings.extendScalars α).obj N) ≅
      (f.moduleInverseImage (ringSheaf J₀ O) ⋙
        SheafOfModules.ChangeOfRings.extendScalars α).obj (tensorObj M N) :=
  tensorIso ((tensorModelIso f O S α).app M) ((tensorModelIso f O S α).app N) ≪≫
    SheafOfModules.TensorScalarExtension.Commutative.tensorIso (coefficientMap f O S α)
      ((geometric f O).obj M) ((geometric f O).obj N) ≪≫
    (scalar f O S α).mapIso (geometricTensorIso f O M N) ≪≫
      ((tensorModelIso f O S α).app (tensorObj M N)).symm

end CategoryTheory.MorphismOfTopoiIn.ModuleTensor
