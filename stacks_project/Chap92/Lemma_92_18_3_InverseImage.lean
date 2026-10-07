module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of cotangent complexes along a morphism of topoi

This leaf records the commutative-ring inverse-image functor of a morphism of topoi and the
canonical identification `f⁻¹ L(B/A) ≅ L(f⁻¹B / f⁻¹A)` of cochain complexes of sheaves of
modules over `f⁻¹B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalRing
open CategoryTheory.Sheaf.InternalCommRing
open Opposite
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial ZeroObject IteratedEndofunctor RelativeDerivation

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

/-- Inverse image of commutative ring sheaves along a morphism of topoi. -/
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

/-- Direct image of commutative ring sheaves along a morphism of topoi preserves finite
products, as a right adjoint. -/
instance pushforward_preservesFiniteProducts
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    PreservesFiniteProducts f.pushforward :=
  LeftExactAdjunction.pushforwardPreservesFiniteProducts f

/-- Direct image of commutative ring sheaves along a morphism of topoi. -/
def commRingDirectImage (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD) :
    Sheaf JD CommRingCat.{u} ⥤ Sheaf JC CommRingCat.{u} :=
  InternalCommRing.toInternal ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
      (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
      f.pushforward inferInstance) ⋙
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
        f.pushforward inferInstance)
      (InternalCommRing.fromInternal ⋙
        sheafCompose JC (CategoryTheory.forget CommRingCat.{u})) ≪≫
    Functor.isoWhiskerLeft
      (InternalCommRing.toInternal ⋙
        @Functor.mapCommRingOfFiniteProducts
          (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
          (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
          f.pushforward inferInstance)
      InternalCommRing.fromInternalForgetIso ≪≫
    Functor.associator InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProducts
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        f.pushforward inferInstance)
      (CommRingObjects.forget JC) ≪≫
    Functor.isoWhiskerLeft InternalCommRing.toInternal
      (@Functor.mapCommRingOfFiniteProductsForgetIso
        (Sheaf JD (Type u)) _ _ (sheafBraidedCategory JD)
        (Sheaf JC (Type u)) _ _ (sheafBraidedCategory JC)
        f.pushforward inferInstance) ≪≫
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

/-- Module inverse image along a morphism of topoi is additive. -/
instance moduleInverseImage_additive
    (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD)
    (R : Sheaf JC RingCat.{u}) :
    (f.moduleInverseImage R).Additive :=
  sorry

end CategoryTheory.MorphismOfTopoiIn

namespace SheafOfModules.RingedSite.CotangentComplex.InverseImage

open CategoryTheory.MorphismOfTopoiIn
open Sheaf.InternalModule

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable (f : MorphismOfTopoiIn.{u, u, u, u, u} JC JD)
variable {A B : Sheaf JC CommRingCat.{u}}

/-- Coefficient transport from `f.ringInverseImage` of `ringSheaf JC B` to
`ringSheaf JD (f.commRingInverseImage.obj B)`. -/
def coefficientIso :
    ringSheaf JD (f.commRingInverseImage.obj B) ≅
      f.ringInverseImage.obj (ringSheaf JC B) :=
  f.commRingInverseImageForgetRingIso.app B

/-- The inverse image of `L(φ)`, transported to a complex of sheaves of modules over
`f⁻¹B`. -/
abbrev source (φ : A ⟶ B) :
    CochainComplex
      (SheafOfModules (ringSheaf JD (f.commRingInverseImage.obj B))) ℤ :=
  ((SheafOfModules.restrictScalars (coefficientIso f).hom).mapHomologicalComplex
    (up ℤ)).obj
    (((f.moduleInverseImage (ringSheaf JC B)).mapHomologicalComplex (up ℤ)).obj
      (obj A (Under.mk φ)))

/-- The cotangent complex of the inverse-image homomorphism `f⁻¹φ`. -/
abbrev target (φ : A ⟶ B) :
    CochainComplex
      (SheafOfModules (ringSheaf JD (f.commRingInverseImage.obj B))) ℤ :=
  obj (f.commRingInverseImage.obj A) (Under.mk (f.commRingInverseImage.map φ))

/-- The cohomological degree `-n` term of the inverse-image complex is the inverse image of
the corresponding simplicial tensor term. -/
def sourceXIso (φ : A ⟶ B) (n : ℕ) :
    (source f φ).X (-n) ≅
      (SheafOfModules.restrictScalars (coefficientIso f).hom).obj
        ((f.moduleInverseImage (ringSheaf JC B)).obj
          ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) :=
  (SheafOfModules.restrictScalars (coefficientIso f).hom).mapIso
    ((f.moduleInverseImage (ringSheaf JC B)).mapIso (objXIso A (Under.mk φ) n))

/-- The cohomological degree `-n` term of the target complex is the corresponding simplicial
tensor term of `L(f⁻¹φ)`. -/
def targetXIso (φ : A ⟶ B) (n : ℕ) :
    (target f φ).X (-n) ≅
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) :=
  objXIso (f.commRingInverseImage.obj A)
    (Under.mk (f.commRingInverseImage.map φ)) n

/-- The inverse-image complex vanishes in strictly positive cohomological degrees. -/
theorem isZero_source_X_of_pos (φ : A ⟶ B) {n : ℤ} (hn : 0 < n) :
    IsZero ((source f φ).X n) :=
  sorry

/-- The target complex vanishes in strictly positive cohomological degrees. -/
theorem isZero_target_X_of_pos (φ : A ⟶ B) {n : ℤ} (hn : 0 < n) :
    IsZero ((target f φ).X n) :=
  sorry



/-- The forgetful functors of the free–forgetful adjunctions commute with inverse image. -/
def forgetfulIso (X : Sheaf JC CommRingCat.{u}) :
    Under.post (X := X) f.commRingInverseImage ⋙
        Under.forget (f.commRingInverseImage.obj X) ⋙
          sheafCompose JD (CategoryTheory.forget CommRingCat.{u}) ≅
      Under.forget X ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{u}) ⋙
        f.inverseImage :=
  Functor.isoWhiskerLeft (Under.forget X) f.commRingInverseImageForgetIso

/-- The mate of the forgetful comparison, as a natural transformation of free algebra
functors. -/
def freeInverseImageNatTrans (X : Sheaf JC CommRingCat.{u}) :
    f.inverseImage ⋙
        Sheaf.composeAndSheafify JD CommRingCat.free ⋙
          Under.costar (f.commRingInverseImage.obj X) ⟶
      Sheaf.composeAndSheafify JC CommRingCat.free ⋙ Under.costar X ⋙
        Under.post f.commRingInverseImage :=
  (mateEquiv (freeForgetAdjunction X)
      (freeForgetAdjunction (f.commRingInverseImage.obj X))).symm
    (forgetfulIso f X).inv





/-- Inverse image of free algebras is canonically isomorphic to free algebras on inverse-image
generators. -/
def freeInverseImageIso (X : Sheaf JC CommRingCat.{u}) :
    f.inverseImage ⋙
        Sheaf.composeAndSheafify JD CommRingCat.free ⋙
          Under.costar (f.commRingInverseImage.obj X) ≅
      Sheaf.composeAndSheafify JC CommRingCat.free ⋙ Under.costar X ⋙
        Under.post f.commRingInverseImage :=
  Adjunction.leftAdjointUniq
    ((f.adjunction.comp
        (freeForgetAdjunction (f.commRingInverseImage.obj X))).ofNatIsoRight
      (Functor.isoWhiskerLeft (Under.forget (f.commRingInverseImage.obj X))
        (commRingDirectImageForgetIso f).symm))
    ((freeForgetAdjunction X).comp
      (Under.postAdjunctionLeft (commRingInverseImageAdjunction f)))

/-- The free–forgetful comonad commutes with inverse image of commutative ring sheaves. -/
def comonadPullbackIso (X : Sheaf JC CommRingCat.{u}) :
    (freeForgetAdjunction X).toComonad.toFunctor ⋙
        Under.post f.commRingInverseImage ≅
      Under.post f.commRingInverseImage ⋙
        (freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor :=
  (Functor.associator
      (Under.forget X ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{u}))
      (Sheaf.composeAndSheafify JC CommRingCat.free ⋙ Under.costar X)
      (Under.post f.commRingInverseImage)).symm ≪≫
    Functor.isoWhiskerLeft
      (Under.forget X ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{u}))
      (freeInverseImageIso f X).symm ≪≫
    Functor.associator
      (Under.forget X ⋙ sheafCompose JC (CategoryTheory.forget CommRingCat.{u}))
      f.inverseImage
      (Sheaf.composeAndSheafify JD CommRingCat.free ⋙
        Under.costar (f.commRingInverseImage.obj X)) ≪≫
    Functor.isoWhiskerRight (forgetfulIso f X).symm
      (Sheaf.composeAndSheafify JD CommRingCat.free ⋙
        Under.costar (f.commRingInverseImage.obj X)) ≪≫
    Functor.associator
      (Under.post f.commRingInverseImage)
      (Under.forget (f.commRingInverseImage.obj X) ⋙
        sheafCompose JD (CategoryTheory.forget CommRingCat.{u}))
      (Sheaf.composeAndSheafify JD CommRingCat.free ⋙
        Under.costar (f.commRingInverseImage.obj X))

/-- Positive iterates of the free–forgetful comonad commute with inverse image. -/
def iteratePullbackIso (X : Sheaf JC CommRingCat.{u}) :
    ∀ n : ℕ,
      (freeForgetAdjunction X).toComonad.toFunctor ⁺⦋n⦌ ⋙
          Under.post f.commRingInverseImage ≅
        Under.post f.commRingInverseImage ⋙
          (freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor ⁺⦋n⦌
  | 0 =>
      Functor.isoWhiskerRight
          (Endofunctor.iterate.oneIso
            (freeForgetAdjunction X).toComonad.toFunctor)
          (Under.post f.commRingInverseImage) ≪≫
        comonadPullbackIso f X ≪≫
        Functor.isoWhiskerLeft (Under.post f.commRingInverseImage)
          (Endofunctor.iterate.oneIso
            (freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor).symm
  | n + 1 =>
      Functor.isoWhiskerRight
          (IteratedEndofunctor.prependIso
            (freeForgetAdjunction X).toComonad.toFunctor n).symm
          (Under.post f.commRingInverseImage) ≪≫
        (Functor.associator
          (freeForgetAdjunction X).toComonad.toFunctor
          ((freeForgetAdjunction X).toComonad.toFunctor ⁺⦋n⦌)
          (Under.post f.commRingInverseImage)).symm ≪≫
        Functor.isoWhiskerLeft (freeForgetAdjunction X).toComonad.toFunctor
          (iteratePullbackIso X n) ≪≫
        Functor.associator
          (freeForgetAdjunction X).toComonad.toFunctor
          (Under.post f.commRingInverseImage)
          ((freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor ⁺⦋n⦌) ≪≫
        Functor.isoWhiskerRight (comonadPullbackIso f X)
          ((freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor ⁺⦋n⦌) ≪≫
        (Functor.associator
          (Under.post f.commRingInverseImage)
          (freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor
          ((freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor ⁺⦋n⦌)).symm ≪≫
        Functor.isoWhiskerLeft (Under.post f.commRingInverseImage)
          (IteratedEndofunctor.prependIso
            (freeForgetAdjunction (f.commRingInverseImage.obj X)).toComonad.toFunctor n)

/-- Inverse image of a standard-resolution term, as an algebra under `f⁻¹A`. -/
abbrev pulledTerm (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    Under (f.commRingInverseImage.obj A) :=
  (Under.post f.commRingInverseImage).obj (standardTerm A (Under.mk φ) n)

/-- The standard-resolution term of the inverse-image homomorphism. -/
abbrev targetTerm (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    Under (f.commRingInverseImage.obj A) :=
  standardTerm (f.commRingInverseImage.obj A)
    (Under.mk (f.commRingInverseImage.map φ)) n

/-- Inverse image identifies standard-resolution terms with the standard-resolution terms of
the inverse-image homomorphism. -/
def standardTermIso (φ : A ⟶ B) (n : ℕ) :
    pulledTerm f φ (op ⦋n⦌) ≅ targetTerm f φ (op ⦋n⦌) :=
  (iteratePullbackIso f A n).app (Under.mk φ)

/-- Inverse image of the standard-resolution augmentation. -/
abbrev pulledAugmentation (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (pulledTerm f φ n).right ⟶ f.commRingInverseImage.obj B :=
  f.commRingInverseImage.map (standardAugmentation A (Under.mk φ) n)

/-- Inverse image of a simplicial tensor term, before transporting along `standardTermIso`. -/
abbrev pulledTensor (φ : A ⟶ B) (n : ℕ) :
    SheafOfModules (ringSheaf JD (f.commRingInverseImage.obj B)) :=
  conormalTensorTerm (pulledTerm f φ (op ⦋n⦌)).hom (pulledAugmentation f φ (op ⦋n⦌))

/-- Restriction of scalars does not change the underlying type-valued sheaf. -/
def restrictScalarsUnderlyingHom {R R' : Sheaf JD RingCat.{u}}
    (α : R ⟶ R') (M : SheafOfModules.{u} R') :
    (ToInternal.underlying R).obj ((SheafOfModules.restrictScalars α).obj M) ⟶
      (ToInternal.underlying R').obj M where
  hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }

/-- The inverse of `restrictScalarsUnderlyingHom`. -/
def restrictScalarsUnderlyingInv {R R' : Sheaf JD RingCat.{u}}
    (α : R ⟶ R') (M : SheafOfModules.{u} R') :
    (ToInternal.underlying R').obj M ⟶
      (ToInternal.underlying R).obj ((SheafOfModules.restrictScalars α).obj M) where
  hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }

/-- Underlying type-valued sheaf of the universal derivation of a ring-sheaf homomorphism. -/
def universalDerivationCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (sheafCompose JC (CategoryTheory.forget CommRingCat.{u})).obj Y ⟶
      (ToInternal.underlying (ringSheaf JC Y)).obj (relativeDifferentials ψ) where
  hom :=
    { app := fun U ↦
        ↾fun y ↦
          (ToInternal.sectionEquiv (ringSheaf JC Y) (relativeDifferentials ψ) U).symm
            ((relativeDifferential ψ).d y)
      naturality := fun _ _ _ ↦ sorry }

/-- Inverse image of the universal derivation, as a map of type-valued sheaves on `D`. -/
def differentialsInverseImageCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (sheafCompose JD (CategoryTheory.forget CommRingCat.{u})).obj
        (f.commRingInverseImage.obj Y) ⟶
      (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj Y))).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Y).hom).obj
          ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ))) :=
  f.commRingInverseImageForgetIso.hom.app Y ≫
    f.inverseImage.map (universalDerivationCarrier ψ) ≫
      (f.moduleInverseImageForgetIso (ringSheaf JC Y)).inv.app (relativeDifferentials ψ) ≫
        restrictScalarsUnderlyingInv
          (f.commRingInverseImageForgetRingIso.app Y).hom
          ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ))

/-- The inverse-image module of `Ω(ψ)` as a derivation target over `f⁻¹Y`. -/
def differentialsInverseImageDerivation {X Y : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) :
    SheafOfModules.RelativeDerivation (f.commRingInverseImage.map ψ)
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ))) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦
      ModuleCat.Derivation.mk
        (fun y ↦
          (ToInternal.sectionEquiv
              (ringSheaf JD (f.commRingInverseImage.obj Y))
              ((SheafOfModules.restrictScalars
                  (f.commRingInverseImageForgetRingIso.app Y).hom).obj
                ((f.moduleInverseImage (ringSheaf JC Y)).obj
                  (relativeDifferentials ψ)))
              U)
            ((differentialsInverseImageCarrier f ψ).hom.app U y))
        (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry))
    (fun _ _ _ _ ↦ sorry)

/-- The inverse comparison on relative differentials, from the universal property of
`Ω(f⁻¹ψ)`. -/
def differentialsIsoInv {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    relativeDifferentials (f.commRingInverseImage.map ψ) ⟶
      (SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) :=
  relativeDifferentialDesc (f.commRingInverseImage.map ψ)
    (differentialsInverseImageDerivation f ψ)

/-- Coefficient transport of `Ω(f⁻¹ψ)` back to a module over `f.ringInverseImage`. -/
abbrev differentialsPushforwardCoeff {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules (f.ringInverseImage.obj (ringSheaf JC Y)) :=
  (SheafOfModules.restrictScalars
      (f.commRingInverseImageForgetRingIso.app Y).inv).obj
    (relativeDifferentials (f.commRingInverseImage.map ψ))

/-- Direct image of `Ω(f⁻¹ψ)` as a module over the original ring sheaf of `Y`. -/
abbrev differentialsPushforwardTarget {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules (ringSheaf JC Y) :=
  (f.moduleRightOver (ringSheaf JC Y)).obj (differentialsPushforwardCoeff f ψ)

/-- The universal derivation of `f⁻¹ψ`, transposed to a type-valued map on `C`. -/
def differentialsPushforwardCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (sheafCompose JC (CategoryTheory.forget CommRingCat.{u})).obj Y ⟶
      (ToInternal.underlying (ringSheaf JC Y)).obj
        (differentialsPushforwardTarget f ψ) :=
  f.adjunction.homEquiv _ _
      (f.commRingInverseImageForgetIso.inv.app Y ≫
        universalDerivationCarrier (f.commRingInverseImage.map ψ) ≫
          restrictScalarsUnderlyingInv
            (f.commRingInverseImageForgetRingIso.app Y).inv
            (relativeDifferentials (f.commRingInverseImage.map ψ))) ≫
    (f.moduleRightOverForgetIso (ringSheaf JC Y)).inv.app
      (differentialsPushforwardCoeff f ψ)

/-- The universal derivation of `f⁻¹ψ`, viewed as a `ψ`-derivation with values in the
pushforward module. -/
def differentialsPushforwardDerivation {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules.RelativeDerivation ψ (differentialsPushforwardTarget f ψ) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦
      ModuleCat.Derivation.mk
        (fun y ↦
          (ToInternal.sectionEquiv (ringSheaf JC Y)
              (differentialsPushforwardTarget f ψ) U)
            ((differentialsPushforwardCarrier f ψ).hom.app U y))
        (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry))
    (fun _ _ _ _ ↦ sorry)

/-- The forward comparison on relative differentials, obtained by transposing the
pushforward of `Ω(f⁻¹ψ)`. -/
def differentialsIsoHom {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) ⟶
    relativeDifferentials (f.commRingInverseImage.map ψ) :=
  (SheafOfModules.restrictScalars
      (f.commRingInverseImageForgetRingIso.app Y).hom).map
    (f.moduleUnmate (ringSheaf JC Y) (relativeDifferentials ψ)
      (differentialsPushforwardCoeff f ψ)
      (relativeDifferentialDesc ψ (differentialsPushforwardDerivation f ψ))) ≫
    (SheafOfModules.Restriction.compIso'
        (f.commRingInverseImageForgetRingIso.app Y).hom
        (f.commRingInverseImageForgetRingIso.app Y).inv
        (𝟙 _)
        (Iso.hom_inv_id (f.commRingInverseImageForgetRingIso.app Y)).symm).hom.app
      (relativeDifferentials (f.commRingInverseImage.map ψ)) ≫
    (SheafOfModules.Restriction.idIso
        (ringSheaf JD (f.commRingInverseImage.obj Y))).inv.app
      (relativeDifferentials (f.commRingInverseImage.map ψ))

/-- Inverse image of relative differentials along a morphism of topoi. -/
def differentialsIso {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) ≅
    relativeDifferentials (f.commRingInverseImage.map ψ) where
  hom := differentialsIsoHom f ψ
  inv := differentialsIsoInv f ψ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction of scalars after inverse image commutes with restriction along a ring-sheaf
homomorphism, on underlying type-valued sheaves. -/
def tensorRestrictionCommuteUnderlying {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj Y))).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj
          ((restrictionAlong α).obj (conormalTensorTerm ψ α)))) ⟶
    (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj Y))).obj
      ((restrictionAlong (f.commRingInverseImage.map α)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).hom).obj
          ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α)))) :=
  restrictScalarsUnderlyingHom
      (f.commRingInverseImageForgetRingIso.app Y).hom
      ((f.moduleInverseImage (ringSheaf JC Y)).obj
        ((restrictionAlong α).obj (conormalTensorTerm ψ α))) ≫
    (f.moduleInverseImageForgetIso (ringSheaf JC Y)).hom.app
      ((restrictionAlong α).obj (conormalTensorTerm ψ α)) ≫
    f.inverseImage.map
      (restrictScalarsUnderlyingHom (ringSheafMap α) (conormalTensorTerm ψ α)) ≫
    (f.moduleInverseImageForgetIso (ringSheaf JC Z)).inv.app (conormalTensorTerm ψ α) ≫
    restrictScalarsUnderlyingInv
      (f.commRingInverseImageForgetRingIso.app Z).hom
      ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α)) ≫
    restrictScalarsUnderlyingInv (ringSheafMap (f.commRingInverseImage.map α))
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α)))

/-- Restriction of scalars after inverse image commutes with restriction along a ring-sheaf
homomorphism. -/
def tensorRestrictionCommute {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj
        ((restrictionAlong α).obj (conormalTensorTerm ψ α))) ⟶
    (restrictionAlong (f.commRingInverseImage.map α)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α))) :=
  homOfUnderlying (ringSheaf JD (f.commRingInverseImage.obj Y))
    (tensorRestrictionCommuteUnderlying f ψ α) sorry sorry

/-- The extension-of-scalars unit, after inverse image and coefficient transport. -/
def tensorInverseImageUnit {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) ⟶
    (restrictionAlong (f.commRingInverseImage.map α)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α))) :=
  (SheafOfModules.restrictScalars
      (f.commRingInverseImageForgetRingIso.app Y).hom).map
    ((f.moduleInverseImage (ringSheaf JC Y)).map
      ((extendRestrictAdj α).unit.app (relativeDifferentials ψ))) ≫
    tensorRestrictionCommute f ψ α

/-- Direct image of a restricted inverse-image module, as a type-valued sheaf on `C`. -/
def tensorRightOverRestrictionUnderlying {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (ToInternal.underlying (ringSheaf JC Y)).obj
      ((f.moduleRightOver (ringSheaf JC Y)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Y).inv).obj
          ((restrictionAlong (f.commRingInverseImage.map α)).obj
            (conormalTensorTerm (f.commRingInverseImage.map ψ)
              (f.commRingInverseImage.map α))))) ⟶
    (ToInternal.underlying (ringSheaf JC Y)).obj
      ((restrictionAlong α).obj
        ((f.moduleRightOver (ringSheaf JC Z)).obj
          ((SheafOfModules.restrictScalars
              (f.commRingInverseImageForgetRingIso.app Z).inv).obj
            (conormalTensorTerm (f.commRingInverseImage.map ψ)
              (f.commRingInverseImage.map α))))) :=
  (f.moduleRightOverForgetIso (ringSheaf JC Y)).hom.app
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).inv).obj
        ((restrictionAlong (f.commRingInverseImage.map α)).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α)))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingHom
        (f.commRingInverseImageForgetRingIso.app Y).inv
        ((restrictionAlong (f.commRingInverseImage.map α)).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α)))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingHom
        (ringSheafMap (f.commRingInverseImage.map α))
        (conormalTensorTerm (f.commRingInverseImage.map ψ)
          (f.commRingInverseImage.map α))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingInv
        (f.commRingInverseImageForgetRingIso.app Z).inv
        (conormalTensorTerm (f.commRingInverseImage.map ψ)
          (f.commRingInverseImage.map α))) ≫
    (f.moduleRightOverForgetIso (ringSheaf JC Z)).inv.app
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).inv).obj
        (conormalTensorTerm (f.commRingInverseImage.map ψ)
          (f.commRingInverseImage.map α))) ≫
    restrictScalarsUnderlyingInv (ringSheafMap α)
      ((f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α))))

/-- Direct image commutes with restriction along a ring-sheaf homomorphism. -/
def tensorRightOverRestrictionCommute {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (f.moduleRightOver (ringSheaf JC Y)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).inv).obj
        ((restrictionAlong (f.commRingInverseImage.map α)).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α)))) ⟶
    (restrictionAlong α).obj
      ((f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α)))) :=
  homOfUnderlying (ringSheaf JC Y)
    (tensorRightOverRestrictionUnderlying f ψ α) sorry sorry

/-- The source tensor term, mapped into the direct image of the inverse-image tensor term. -/
def tensorPushforwardMap {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    conormalTensorTerm ψ α ⟶
      (f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α))) :=
  ((extendRestrictAdj α).homEquiv _ _).symm
    (relativeDifferentialDesc ψ (differentialsPushforwardDerivation f ψ) ≫
      (f.moduleRightOver (ringSheaf JC Y)).map
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Y).inv).map
          ((extendRestrictAdj (f.commRingInverseImage.map α)).unit.app
            (relativeDifferentials (f.commRingInverseImage.map ψ)))) ≫
      tensorRightOverRestrictionCommute f ψ α)

/-- Inverse image of a conormal tensor term, after coefficient transport to `f⁻¹Z`. -/
def tensorInverseImageIso {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Z)).obj (conormalTensorTerm ψ α)) ≅
    conormalTensorTerm (f.commRingInverseImage.map ψ)
      (f.commRingInverseImage.map α) where
  hom :=
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).map
      (f.moduleUnmate (ringSheaf JC Z) (conormalTensorTerm ψ α)
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          (conormalTensorTerm (f.commRingInverseImage.map ψ)
            (f.commRingInverseImage.map α)))
        (tensorPushforwardMap f ψ α)) ≫
    (SheafOfModules.Restriction.compIso'
        (f.commRingInverseImageForgetRingIso.app Z).hom
        (f.commRingInverseImageForgetRingIso.app Z).inv
        (𝟙 _)
        (Iso.hom_inv_id (f.commRingInverseImageForgetRingIso.app Z)).symm).hom.app
      (conormalTensorTerm (f.commRingInverseImage.map ψ)
        (f.commRingInverseImage.map α)) ≫
    (SheafOfModules.Restriction.idIso
        (ringSheaf JD (f.commRingInverseImage.obj Z))).inv.app
      (conormalTensorTerm (f.commRingInverseImage.map ψ)
        (f.commRingInverseImage.map α))
  inv :=
    ((extendRestrictAdj (f.commRingInverseImage.map α)).homEquiv _ _).symm
      ((differentialsIso f ψ).inv ≫ tensorInverseImageUnit f ψ α)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The pulled tensor term and the target tensor term are related by `standardTermIso`. -/
theorem pulledAugmentation_comp_ringSheaf (φ : A ⟶ B) (n : ℕ) :
    ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)) =
      ringSheafMap (standardTermIso f φ n).hom.right ≫
        ringSheafMap
          (standardAugmentation (f.commRingInverseImage.obj A)
            (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)) :=
  sorry

/-- The inverse of `pulledAugmentation_comp_ringSheaf`. -/
theorem pulledAugmentation_comp_ringSheaf_inv (φ : A ⟶ B) (n : ℕ) :
    ringSheafMap
      (standardAugmentation (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)) =
      ringSheafMap (standardTermIso f φ n).inv.right ≫
        ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)) :=
  sorry

/-- Degreewise comparison of pulled tensor terms with the tensor terms of `L(f⁻¹φ)`. -/
def standardTermTensorIso (φ : A ⟶ B) (n : ℕ) :
    pulledTensor f φ n ≅
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) where
  hom :=
    ((extendRestrictAdj (pulledAugmentation f φ (op ⦋n⦌))).homEquiv _ _).symm
      (RelativeDifferentials.map
          ⟨(Category.id_comp (targetTerm f φ (op ⦋n⦌)).hom).trans
            (standardTermIso f φ n).hom.w.symm⟩ ≫
        (restrictionAlong (standardTermIso f φ n).hom.right).map
          ((extendRestrictAdj
              (standardAugmentation (f.commRingInverseImage.obj A)
                (Under.mk (f.commRingInverseImage.map φ))
                (op ⦋n⦌))).unit.app
            (relativeDifferentials (targetTerm f φ (op ⦋n⦌)).hom)) ≫
          (SheafOfModules.Restriction.compIso'
              (ringSheafMap (standardTermIso f φ n).hom.right)
              (ringSheafMap
                (standardAugmentation (f.commRingInverseImage.obj A)
                  (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)))
              (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))
              (pulledAugmentation_comp_ringSheaf f φ n)).hom.app _)
  inv :=
    ((extendRestrictAdj
          (standardAugmentation (f.commRingInverseImage.obj A)
            (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌))).homEquiv _ _).symm
      (RelativeDifferentials.map
          ⟨(Category.id_comp (pulledTerm f φ (op ⦋n⦌)).hom).trans
            (standardTermIso f φ n).inv.w.symm⟩ ≫
        (restrictionAlong (standardTermIso f φ n).inv.right).map
          ((extendRestrictAdj (pulledAugmentation f φ (op ⦋n⦌))).unit.app
            (relativeDifferentials (pulledTerm f φ (op ⦋n⦌)).hom)) ≫
          (SheafOfModules.Restriction.compIso'
              (ringSheafMap (standardTermIso f φ n).inv.right)
              (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))
              (ringSheafMap
                (standardAugmentation (f.commRingInverseImage.obj A)
                  (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)))
              (pulledAugmentation_comp_ringSheaf_inv f φ n)).hom.app _)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Degreewise comparison of inverse-image simplicial tensor terms with the simplicial
tensor terms of `L(f⁻¹φ)`. -/
def termIso (φ : A ⟶ B) (n : ℕ) :
    (SheafOfModules.restrictScalars (coefficientIso f).hom).obj
        ((f.moduleInverseImage (ringSheaf JC B)).obj
          ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))) ≅
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) :=
  tensorInverseImageIso f (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom
      (standardAugmentation A (Under.mk φ) (op ⦋n⦌)) ≪≫
    standardTermTensorIso f φ n

/-- Degreewise comparison of the inverse-image and target cotangent complexes. -/
def appIso (φ : A ⟶ B) :
    ∀ n : ℤ, (source f φ).X n ≅ (target f φ).X n
  | Int.ofNat (Nat.succ k) =>
      { hom := (0 : (source f φ).X (Int.ofNat k.succ) ⟶ (target f φ).X (Int.ofNat k.succ))
        inv := (0 : (target f φ).X (Int.ofNat k.succ) ⟶ (source f φ).X (Int.ofNat k.succ))
        hom_inv_id := sorry
        inv_hom_id := sorry }
  | (0 : ℤ) =>
      (sourceXIso f φ 0).trans ((termIso f φ 0).trans (targetXIso f φ 0).symm)
  | Int.negSucc k =>
      (sourceXIso f φ k.succ).trans
        ((termIso f φ k.succ).trans (targetXIso f φ k.succ).symm)

/-- The canonical identification `f⁻¹ L(φ) ≅ L(f⁻¹φ)` of cochain complexes of
`f⁻¹B`-modules. -/
def iso (φ : A ⟶ B) : source f φ ≅ target f φ :=
  HomologicalComplex.Hom.isoOfComponents (appIso f φ) (fun _ _ _ ↦ sorry)

/-- The forward comparison morphism of inverse-image cotangent complexes. -/
def map (φ : A ⟶ B) : source f φ ⟶ target f φ :=
  (iso f φ).hom

/-- The inverse comparison morphism of inverse-image cotangent complexes. -/
def mapInv (φ : A ⟶ B) : target f φ ⟶ source f φ :=
  (iso f φ).inv

/-- The canonical comparison morphism is an isomorphism. -/
instance map_isIso (φ : A ⟶ B) : IsIso (map f φ) :=
  (iso f φ).isIso_hom

/-- In cohomological degree `-n`, the comparison is the inverse-image comparison of
simplicial tensor terms. -/
theorem iso_hom_f (φ : A ⟶ B) (n : ℕ) :
    (iso f φ).hom.f (-n) =
      (sourceXIso f φ n).hom ≫ (termIso f φ n).hom ≫ (targetXIso f φ n).inv :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex.InverseImage
