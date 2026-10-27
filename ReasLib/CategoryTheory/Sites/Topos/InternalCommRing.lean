/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse and direct image of commutative-ring sheaves

This module transports commutative-ring sheaves along a morphism of topoi and records the
underlying-ring comparisons and the resulting adjunction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open CategoryTheory.Sheaf.InternalCommRing

noncomputable section

universe u

namespace CategoryTheory.MorphismOfTopoiIn

section InverseImage

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [JD.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- Inverse image of commutative ring sheaves along a geometric morphism of topoi. -/
def commRingInverseImage (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    Sheaf JC CommRingCat.{w} ⥤ Sheaf JD CommRingCat.{w} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
      (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
      f.inverseImage inferInstance) ⋙
    InternalCommRing.fromInternal

/-- Forgetting commutativity after commutative-ring inverse image recovers ring-valued
inverse image. -/
def commRingInverseImageForgetRingIso
    (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    f.commRingInverseImage ⋙ CommRingSheaves.forgetRing (J := JD) ≅
      CommRingSheaves.forgetRing (J := JC) ⋙ f.ringInverseImage :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (InternalCommRing.fromInternal ⋙ CommRingSheaves.forgetRing (J := JD)) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
      (InternalCommRing.fromInternalForgetRingIso (J := JD)) ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      ((CommRingObjects.forgetRing JD) ⋙ InternalRing.fromInternal) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (Functor.isoWhiskerRight
        (@Functor.mapCommRingOfFiniteProductsForgetRingIso
          (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
        InternalRing.fromInternal) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forgetRing JC)
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal)).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetRingIso
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal) ≪≫
    Functor.associator (CommRingSheaves.forgetRing (J := JC)) InternalRing.toInternal
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal)

end InverseImage

universe uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [JD.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]

/-- Forgetting to type-valued sheaves after commutative-ring inverse image recovers type-valued
inverse image. -/
def commRingInverseImageForgetIso
    (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    f.commRingInverseImage ⋙ sheafCompose JD (CategoryTheory.forget CommRingCat.{w}) ≅
      sheafCompose JC (CategoryTheory.forget CommRingCat.{w}) ⋙ f.inverseImage :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (InternalCommRing.fromInternal ⋙
        sheafCompose JD (CategoryTheory.forget CommRingCat.{w})) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
      InternalCommRing.fromInternalForgetIso ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (CommRingObjects.forget JD) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProductsForgetIso
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forget JC)
      f.inverseImage).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetIso f.inverseImage

/-- Direct image of commutative ring sheaves along a morphism of topoi. -/
def commRingDirectImage (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    Sheaf JD CommRingCat.{w} ⥤ Sheaf JC CommRingCat.{w} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
      (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
      f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)) ⋙
    InternalCommRing.fromInternal

/-- Forgetting to type-valued sheaves after commutative-ring direct image recovers type-valued
direct image. -/
def commRingDirectImageForgetIso
    (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    f.commRingDirectImage ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{w}) ≅
      sheafCompose JD (CategoryTheory.forget CommRingCat.{w}) ⋙ f.pushforward :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      (InternalCommRing.fromInternal ⋙
        sheafCompose JC (CategoryTheory.forget CommRingCat.{w})) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
          (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
          f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      InternalCommRing.fromInternalForgetIso ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      (CommRingObjects.forget JC) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProductsForgetIso
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forget JD)
      f.pushforward).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetIso f.pushforward

/-- Commutative-ring inverse image is left adjoint to commutative-ring direct image. -/
def commRingInverseImageAdjunction
    (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD) :
    f.commRingInverseImage ⊣ f.commRingDirectImage :=
  (((InternalCommRing.equivalence (J := JC)).toAdjunction.comp
      (@Functor.mapCommRingOfFiniteProductsAdjunction
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance f.pushforward
          (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) f.adjunction)).comp
    (InternalCommRing.equivalence (J := JD)).symm.toAdjunction).ofNatIsoLeft
    (Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type w)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type w)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      InternalCommRing.fromInternal)

section Composition

universe uE vE
variable {E : Type uE} [Category.{vE} E] {JE : GrothendieckTopology E}
variable [JE.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JE.HasSheafCompose (forget RingCat.{w})]

/-- Inverse image of a commutative ring sheaf along a composite is successive inverse image. -/
def commRingInverseImageCompIso
    (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD)
    (g : MorphismOfTopoiIn.{uD, uE, vD, vE, w} JD JE)
    (A : Sheaf JC CommRingCat.{w}) :
    (MorphismOfTopoiIn.comp f g).commRingInverseImage.obj A ≅
      g.commRingInverseImage.obj (f.commRingInverseImage.obj A) :=
  (CommRingSheaves.fullyFaithfulForgetRing (J := JE)).preimageIso
    ((MorphismOfTopoiIn.comp f g).commRingInverseImageForgetRingIso.app A ≪≫
      (ringInverseImageCompIso f g).app (CommRingSheaves.forgetRing.obj A) ≪≫
      g.ringInverseImage.mapIso (f.commRingInverseImageForgetRingIso.app A).symm ≪≫
      (g.commRingInverseImageForgetRingIso.app (f.commRingInverseImage.obj A)).symm)

end Composition

end CategoryTheory.MorphismOfTopoiIn

end
