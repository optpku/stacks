/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]

/-- Inverse image of commutative ring sheaves along a geometric morphism of topoi. -/
def commRingInverseImage (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    Sheaf JC CommRingCat.{u} ⥤ Sheaf JD CommRingCat.{u} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
      (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
      f.inverseImage inferInstance) ⋙
    InternalCommRing.fromInternal

/-- Forgetting commutativity after commutative-ring inverse image recovers ring-valued
inverse image. -/
def commRingInverseImageForgetRingIso
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    f.commRingInverseImage ⋙ CommRingSheaves.forgetRing (J := JD) ≅
      CommRingSheaves.forgetRing (J := JC) ⋙ f.ringInverseImage :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (InternalCommRing.fromInternal ⋙ CommRingSheaves.forgetRing (J := JD)) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
      (InternalCommRing.fromInternalForgetRingIso (J := JD)) ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      ((CommRingObjects.forgetRing JD) ⋙ InternalRing.fromInternal) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (Functor.isoWhiskerRight
        (@Functor.mapCommRingOfFiniteProductsForgetRingIso
          (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
        InternalRing.fromInternal) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forgetRing JC)
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal)).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetRingIso
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal) ≪≫
    Functor.associator (CommRingSheaves.forgetRing (J := JC)) InternalRing.toInternal
      (f.internalRingInverseImage ⋙ InternalRing.fromInternal)

/-- Forgetting to type-valued sheaves after commutative-ring inverse image recovers type-valued
inverse image. -/
def commRingInverseImageForgetIso
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    f.commRingInverseImage ⋙ sheafCompose JD (CategoryTheory.forget CommRingCat.{u}) ≅
      sheafCompose JC (CategoryTheory.forget CommRingCat.{u}) ⋙ f.inverseImage :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (InternalCommRing.fromInternal ⋙
        sheafCompose JD (CategoryTheory.forget CommRingCat.{u})) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
          (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
          f.inverseImage inferInstance)
      InternalCommRing.fromInternalForgetIso ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      (CommRingObjects.forget JD) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProductsForgetIso
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forget JC)
      f.inverseImage).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetIso f.inverseImage

/-- Direct image of commutative ring sheaves along a morphism of topoi. -/
def commRingDirectImage (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    Sheaf JD CommRingCat.{u} ⥤ Sheaf JC CommRingCat.{u} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
      (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
      f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)) ⋙
    InternalCommRing.fromInternal

/-- Forgetting to type-valued sheaves after commutative-ring direct image recovers type-valued
direct image. -/
def commRingDirectImageForgetIso
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    f.commRingDirectImage ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{u}) ≅
      sheafCompose JD (CategoryTheory.forget CommRingCat.{u}) ⋙ f.pushforward :=
  Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      (InternalCommRing.fromInternal ⋙
        sheafCompose JC (CategoryTheory.forget CommRingCat.{u})) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
          (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
          f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      InternalCommRing.fromInternalForgetIso ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f))
      (CommRingObjects.forget JC) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProductsForgetIso
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        f.pushforward (LeftExactAdjunction.pushforwardPreservesFiniteProducts f)) ≪≫
    (Functor.associator InternalCommRing.toInternal (CommRingObjects.forget JD)
      f.pushforward).symm ≪≫
    Functor.isoWhiskerRight InternalCommRing.toInternalForgetIso f.pushforward

/-- Commutative-ring inverse image is left adjoint to commutative-ring direct image. -/
def commRingInverseImageAdjunction
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    f.commRingInverseImage ⊣ f.commRingDirectImage :=
  (((InternalCommRing.equivalence (J := JC)).toAdjunction.comp
      (@Functor.mapCommRingOfFiniteProductsAdjunction
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance f.pushforward
          (LeftExactAdjunction.pushforwardPreservesFiniteProducts f) f.adjunction)).comp
    (InternalCommRing.equivalence (J := JD)).symm.toAdjunction).ofNatIsoLeft
    (Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        f.inverseImage inferInstance)
      InternalCommRing.fromInternal)

end CategoryTheory.MorphismOfTopoiIn

end
