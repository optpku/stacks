module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.CrossRefAttribute
/-!
# Inverse-image transport for cotangent complexes

This module records the commutative-ring inverse-image functor of a morphism of topoi and the
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
    ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (f.moduleInverseImage (ringSheaf JC B))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (f.moduleInverseImage_additive (ringSheaf JC B))) (up ℤ)).obj
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
private theorem isZero_source_X_of_pos (φ : A ⟶ B) {n : ℤ} (hn : 0 < n) :
    IsZero ((source f φ).X n) :=
  sorry

/-- The target complex vanishes in strictly positive cohomological degrees. -/
private theorem isZero_target_X_of_pos (φ : A ⟶ B) {n : ℤ} (hn : 0 < n) :
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
  (SheafOfModules.ChangeOfRings.extendScalars
      (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))).obj
    (relativeDifferentials (pulledTerm f φ (op ⦋n⦌)).hom)

section

set_option backward.privateInPublic true

/-- Restriction of scalars does not change the underlying type-valued sheaf. -/
private def restrictScalarsUnderlyingHom {R R' : Sheaf JD RingCat.{u}}
    (α : R ⟶ R') (M : SheafOfModules.{u} R') :
    (ToInternal.underlying R).obj ((SheafOfModules.restrictScalars α).obj M) ⟶
      (ToInternal.underlying R').obj M where
  hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }

/-- The inverse of `restrictScalarsUnderlyingHom`. -/
private def restrictScalarsUnderlyingInv {R R' : Sheaf JD RingCat.{u}}
    (α : R ⟶ R') (M : SheafOfModules.{u} R') :
    (ToInternal.underlying R').obj M ⟶
      (ToInternal.underlying R).obj ((SheafOfModules.restrictScalars α).obj M) where
  hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry }

/-- Underlying type-valued sheaf of the universal derivation of a ring-sheaf homomorphism. -/
private def universalDerivationCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (sheafCompose JC (CategoryTheory.forget CommRingCat.{u})).obj Y ⟶
      (ToInternal.underlying (ringSheaf JC Y)).obj (relativeDifferentials ψ) where
  hom :=
    { app := fun U ↦
        ↾fun y ↦
          (ToInternal.sectionEquiv (ringSheaf JC Y) (relativeDifferentials ψ) U).symm
            ((relativeDifferential ψ).d y)
      naturality := fun _ _ _ ↦ sorry }

/-- Inverse image of the universal derivation, as a map of type-valued sheaves on `D`. -/
private def differentialsInverseImageCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
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

/-- The inverse image of the universal derivation preserves addition, satisfies the Leibniz
rule, vanishes on the base, and commutes with restriction. -/
private theorem differentialsInverseImageDerivation_laws {X Y : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) :
    let M : SheafOfModules (ringSheaf JD (f.commRingInverseImage.obj Y)) :=
      (SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ))
    let d : ∀ U : Dᵒᵖ, (f.commRingInverseImage.obj Y).obj.obj U → M.val.obj U :=
      fun U y ↦
          (ToInternal.sectionEquiv
              (ringSheaf JD (f.commRingInverseImage.obj Y))
              ((SheafOfModules.restrictScalars
                  (f.commRingInverseImageForgetRingIso.app Y).hom).obj
                ((f.moduleInverseImage (ringSheaf JC Y)).obj
                  (relativeDifferentials ψ)))
              U)
            ((differentialsInverseImageCarrier f ψ).hom.app U y)
    (∀ U x y, d U (x + y) = d U x + d U y) ∧
    (∀ U x y, d U (x * y) = x • d U y + y • d U x) ∧
    (∀ U (a : (f.commRingInverseImage.obj X).obj.obj U), d U ((f.commRingInverseImage.map ψ).hom.app U a) = 0) ∧
    (∀ {U V : Dᵒᵖ} (i : U ⟶ V) (x : (f.commRingInverseImage.obj Y).obj.obj U),
      d V ((f.commRingInverseImage.obj Y).obj.map i x) = M.val.map i (d U x)) := by
  sorry

/-- The inverse-image module of `Ω(ψ)` as a derivation target over `f⁻¹Y`. -/
private def differentialsInverseImageDerivation {X Y : Sheaf JC CommRingCat.{u}}
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
        ((differentialsInverseImageDerivation_laws f ψ).1 U)
        ((differentialsInverseImageDerivation_laws f ψ).2.1 U)
        ((differentialsInverseImageDerivation_laws f ψ).2.2.1 U))
    (fun _ _ i x ↦ (differentialsInverseImageDerivation_laws f ψ).2.2.2 i x)

/-- The inverse comparison on relative differentials, from the universal property of
`Ω(f⁻¹ψ)`. -/
private def differentialsIsoInv {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    relativeDifferentials (f.commRingInverseImage.map ψ) ⟶
      (SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) :=
  relativeDifferentialDesc (f.commRingInverseImage.map ψ)
    (differentialsInverseImageDerivation f ψ)

/-- Coefficient transport of `Ω(f⁻¹ψ)` back to a module over `f.ringInverseImage`. -/
private abbrev differentialsPushforwardCoeff {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules (f.ringInverseImage.obj (ringSheaf JC Y)) :=
  (SheafOfModules.restrictScalars
      (f.commRingInverseImageForgetRingIso.app Y).inv).obj
    (relativeDifferentials (f.commRingInverseImage.map ψ))

/-- Direct image of `Ω(f⁻¹ψ)` as a module over the original ring sheaf of `Y`. -/
private abbrev differentialsPushforwardTarget {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules (ringSheaf JC Y) :=
  (f.moduleRightOver (ringSheaf JC Y)).obj (differentialsPushforwardCoeff f ψ)

/-- The universal derivation of `f⁻¹ψ`, transposed to a type-valued map on `C`. -/
private def differentialsPushforwardCarrier {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
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

/-- The adjoint of the inverse-image universal derivation preserves addition, satisfies the
Leibniz rule, vanishes on the base, and commutes with restriction. -/
private theorem differentialsPushforwardDerivation_laws {X Y : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) :
    let M : SheafOfModules (ringSheaf JC (Y)) :=
      differentialsPushforwardTarget f ψ
    let d : ∀ U : Cᵒᵖ, (Y).obj.obj U → M.val.obj U :=
      fun U y ↦
          (ToInternal.sectionEquiv (ringSheaf JC Y)
              (differentialsPushforwardTarget f ψ) U)
            ((differentialsPushforwardCarrier f ψ).hom.app U y)
    (∀ U x y, d U (x + y) = d U x + d U y) ∧
    (∀ U x y, d U (x * y) = x • d U y + y • d U x) ∧
    (∀ U (a : (X).obj.obj U), d U ((ψ).hom.app U a) = 0) ∧
    (∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : (Y).obj.obj U),
      d V ((Y).obj.map i x) = M.val.map i (d U x)) := by
  sorry

/-- The universal derivation of `f⁻¹ψ`, viewed as a `ψ`-derivation with values in the
pushforward module. -/
private def differentialsPushforwardDerivation {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    SheafOfModules.RelativeDerivation ψ (differentialsPushforwardTarget f ψ) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦
      ModuleCat.Derivation.mk
        (fun y ↦
          (ToInternal.sectionEquiv (ringSheaf JC Y)
              (differentialsPushforwardTarget f ψ) U)
            ((differentialsPushforwardCarrier f ψ).hom.app U y))
        ((differentialsPushforwardDerivation_laws f ψ).1 U)
        ((differentialsPushforwardDerivation_laws f ψ).2.1 U)
        ((differentialsPushforwardDerivation_laws f ψ).2.2.1 U))
    (fun _ _ i x ↦ (differentialsPushforwardDerivation_laws f ψ).2.2.2 i x)

/-- The forward comparison on relative differentials, obtained by transposing the
pushforward of `Ω(f⁻¹ψ)`. -/
private def differentialsIsoHom {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
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

/-- The canonical forward and reverse comparisons of relative differentials are inverse. -/
private theorem differentialsIso_laws {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    differentialsIsoHom f ψ ≫ differentialsIsoInv f ψ = 𝟙 _ ∧
      differentialsIsoInv f ψ ≫ differentialsIsoHom f ψ = 𝟙 _ := by
  sorry

/-- Inverse image of relative differentials along a morphism of topoi. -/
private def differentialsIso {X Y : Sheaf JC CommRingCat.{u}} (ψ : X ⟶ Y) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) ≅
    relativeDifferentials (f.commRingInverseImage.map ψ) where
  hom := differentialsIsoHom f ψ
  inv := differentialsIsoInv f ψ
  hom_inv_id := (differentialsIso_laws f ψ).1
  inv_hom_id := (differentialsIso_laws f ψ).2

/-- Restriction of scalars after inverse image commutes with restriction along a ring-sheaf
homomorphism, on underlying type-valued sheaves. -/
private def tensorRestrictionCommuteUnderlying {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj Y))).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Y)).obj
          ((restrictionAlong α).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                       (relativeDifferentials ψ))))) ⟶
    (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj Y))).obj
      ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).hom).obj
          ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                          (relativeDifferentials ψ))))) :=
  restrictScalarsUnderlyingHom
      (f.commRingInverseImageForgetRingIso.app Y).hom
      ((f.moduleInverseImage (ringSheaf JC Y)).obj
        ((restrictionAlong α).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                     (relativeDifferentials ψ)))) ≫
    (f.moduleInverseImageForgetIso (ringSheaf JC Y)).hom.app
      ((restrictionAlong α).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                   (relativeDifferentials ψ))) ≫
    f.inverseImage.map
      (restrictScalarsUnderlyingHom (ringSheafMap α) ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                        (relativeDifferentials ψ))) ≫
    (f.moduleInverseImageForgetIso (ringSheaf JC Z)).inv.app ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                                (relativeDifferentials ψ)) ≫
    restrictScalarsUnderlyingInv
      (f.commRingInverseImageForgetRingIso.app Z).hom
      ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                      (relativeDifferentials ψ))) ≫
    restrictScalarsUnderlyingInv (ringSheafMap (f.commRingInverseImage.map α))
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                        (relativeDifferentials ψ))))

/-- The canonical comparison of underlying sheaves preserves addition and scalar
multiplication on sections. -/
private theorem tensorRestrictionCommute_linear {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    let M : SheafOfModules (ringSheaf JD (f.commRingInverseImage.obj Y)) :=
      (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj
        ((restrictionAlong α).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                     (relativeDifferentials ψ))))
    (∀ U (x y : M.val.obj U),
      underlyingApp (ringSheaf JD (f.commRingInverseImage.obj Y)) (tensorRestrictionCommuteUnderlying f ψ α) U (x + y) =
        underlyingApp (ringSheaf JD (f.commRingInverseImage.obj Y)) (tensorRestrictionCommuteUnderlying f ψ α) U x +
          underlyingApp (ringSheaf JD (f.commRingInverseImage.obj Y)) (tensorRestrictionCommuteUnderlying f ψ α) U y) ∧
    (∀ U (r : (ringSheaf JD (f.commRingInverseImage.obj Y)).obj.obj U) (x : M.val.obj U),
      underlyingApp (ringSheaf JD (f.commRingInverseImage.obj Y)) (tensorRestrictionCommuteUnderlying f ψ α) U (r • x) =
        r • underlyingApp (ringSheaf JD (f.commRingInverseImage.obj Y)) (tensorRestrictionCommuteUnderlying f ψ α) U x) := by
  sorry

/-- Restriction of scalars after inverse image commutes with restriction along a ring-sheaf
homomorphism. -/
private def tensorRestrictionCommute {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj
        ((restrictionAlong α).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                     (relativeDifferentials ψ)))) ⟶
    (restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                        (relativeDifferentials ψ)))) :=
  homOfUnderlying (ringSheaf JD (f.commRingInverseImage.obj Y))
    (tensorRestrictionCommuteUnderlying f ψ α)
    (tensorRestrictionCommute_linear f ψ α).1 (tensorRestrictionCommute_linear f ψ α).2

/-- The extension-of-scalars unit, after inverse image and coefficient transport. -/
private def tensorInverseImageUnit {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Y).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Y)).obj (relativeDifferentials ψ)) ⟶
    (restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).hom).obj
        ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                        (relativeDifferentials ψ)))) :=
  (SheafOfModules.restrictScalars
      (f.commRingInverseImageForgetRingIso.app Y).hom).map
    ((f.moduleInverseImage (ringSheaf JC Y)).map
      ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap α)).unit.app
        (relativeDifferentials ψ))) ≫
    tensorRestrictionCommute f ψ α

/-- Direct image of a restricted inverse-image module, as a type-valued sheaf on `C`. -/
private def tensorRightOverRestrictionUnderlying {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (ToInternal.underlying (ringSheaf JC Y)).obj
      ((f.moduleRightOver (ringSheaf JC Y)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Y).inv).obj
          ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
            ((SheafOfModules.ChangeOfRings.extendScalars
              (ringSheafMap (f.commRingInverseImage.map α))).obj
              (relativeDifferentials (f.commRingInverseImage.map ψ)))))) ⟶
    (ToInternal.underlying (ringSheaf JC Y)).obj
      ((restrictionAlong α).obj
        ((f.moduleRightOver (ringSheaf JC Z)).obj
          ((SheafOfModules.restrictScalars
              (f.commRingInverseImageForgetRingIso.app Z).inv).obj
            ((SheafOfModules.ChangeOfRings.extendScalars
            (ringSheafMap (f.commRingInverseImage.map α))).obj
            (    (relativeDifferentials (f.commRingInverseImage.map ψ))))))) :=
  (f.moduleRightOverForgetIso (ringSheaf JC Y)).hom.app
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).inv).obj
        ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ)))))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingHom
        (f.commRingInverseImageForgetRingIso.app Y).inv
        ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ)))))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingHom
        (ringSheafMap (f.commRingInverseImage.map α))
        ((SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap (f.commRingInverseImage.map α))).obj
        (    (relativeDifferentials (f.commRingInverseImage.map ψ))))) ≫
    f.pushforward.map
      (restrictScalarsUnderlyingInv
        (f.commRingInverseImageForgetRingIso.app Z).inv
        ((SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap (f.commRingInverseImage.map α))).obj
        (    (relativeDifferentials (f.commRingInverseImage.map ψ))))) ≫
    (f.moduleRightOverForgetIso (ringSheaf JC Z)).inv.app
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Z).inv).obj
        ((SheafOfModules.ChangeOfRings.extendScalars
        (ringSheafMap (f.commRingInverseImage.map α))).obj
        (    (relativeDifferentials (f.commRingInverseImage.map ψ))))) ≫
    restrictScalarsUnderlyingInv (ringSheafMap α)
      ((f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ))))))

/-- The canonical comparison of underlying sheaves preserves addition and scalar
multiplication on sections. -/
private theorem tensorRightOverRestrictionCommute_linear {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    let M : SheafOfModules (ringSheaf JC Y) :=
      (f.moduleRightOver (ringSheaf JC Y)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).inv).obj
        ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ))))))
    (∀ U (x y : M.val.obj U),
      underlyingApp (ringSheaf JC Y) (tensorRightOverRestrictionUnderlying f ψ α) U (x + y) =
        underlyingApp (ringSheaf JC Y) (tensorRightOverRestrictionUnderlying f ψ α) U x +
          underlyingApp (ringSheaf JC Y) (tensorRightOverRestrictionUnderlying f ψ α) U y) ∧
    (∀ U (r : (ringSheaf JC Y).obj.obj U) (x : M.val.obj U),
      underlyingApp (ringSheaf JC Y) (tensorRightOverRestrictionUnderlying f ψ α) U (r • x) =
        r • underlyingApp (ringSheaf JC Y) (tensorRightOverRestrictionUnderlying f ψ α) U x) := by
  sorry

/-- Direct image commutes with restriction along a ring-sheaf homomorphism. -/
private def tensorRightOverRestrictionCommute {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (f.moduleRightOver (ringSheaf JC Y)).obj
      ((SheafOfModules.restrictScalars
          (f.commRingInverseImageForgetRingIso.app Y).inv).obj
        ((restrictionAlong (J := JD) (f.commRingInverseImage.map α)).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ)))))) ⟶
    (restrictionAlong α).obj
      ((f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ)))))) :=
  homOfUnderlying (ringSheaf JC Y)
    (tensorRightOverRestrictionUnderlying f ψ α)
    (tensorRightOverRestrictionCommute_linear f ψ α).1 (tensorRightOverRestrictionCommute_linear f ψ α).2

/-- The source tensor term, mapped into the direct image of the inverse-image tensor term. -/
private def tensorPushforwardMap {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
      (relativeDifferentials ψ) ⟶
      (f.moduleRightOver (ringSheaf JC Z)).obj
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
          (    (relativeDifferentials (f.commRingInverseImage.map ψ))))) :=
  ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringSheafMap α)).homEquiv _ _).symm
    (relativeDifferentialDesc ψ (differentialsPushforwardDerivation f ψ) ≫
      (f.moduleRightOver (ringSheaf JC Y)).map
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Y).inv).map
          ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
              (ringSheafMap (f.commRingInverseImage.map α))).unit.app
            (relativeDifferentials (f.commRingInverseImage.map ψ)))) ≫
      tensorRightOverRestrictionCommute f ψ α)

/-- The canonical forward comparison of inverse-image tensor terms. -/
private def tensorInverseImageIsoHom {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                      (relativeDifferentials ψ))) ⟶
    (SheafOfModules.ChangeOfRings.extendScalars
      (ringSheafMap (f.commRingInverseImage.map α))).obj
        (relativeDifferentials (f.commRingInverseImage.map ψ)) :=
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).map
      (f.moduleUnmate (ringSheaf JC Z)
        ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
          (relativeDifferentials ψ))
        ((SheafOfModules.restrictScalars
            (f.commRingInverseImageForgetRingIso.app Z).inv).obj
          ((SheafOfModules.ChangeOfRings.extendScalars
              (ringSheafMap (f.commRingInverseImage.map α))).obj
            (relativeDifferentials (f.commRingInverseImage.map ψ))))
        (tensorPushforwardMap f ψ α)) ≫
    (SheafOfModules.Restriction.compIso'
        (f.commRingInverseImageForgetRingIso.app Z).hom
        (f.commRingInverseImageForgetRingIso.app Z).inv
        (𝟙 _)
        (Iso.hom_inv_id (f.commRingInverseImageForgetRingIso.app Z)).symm).hom.app
      ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
        (relativeDifferentials (f.commRingInverseImage.map ψ))) ≫
    (SheafOfModules.Restriction.idIso
        (ringSheaf JD (f.commRingInverseImage.obj Z))).inv.app
      ((SheafOfModules.ChangeOfRings.extendScalars
          (ringSheafMap (f.commRingInverseImage.map α))).obj
        (relativeDifferentials (f.commRingInverseImage.map ψ)))

/-- The canonical reverse comparison of inverse-image tensor terms. -/
private def tensorInverseImageIsoInv {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.ChangeOfRings.extendScalars
      (ringSheafMap (f.commRingInverseImage.map α))).obj
        (relativeDifferentials (f.commRingInverseImage.map ψ)) ⟶
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                      (relativeDifferentials ψ))) :=
    ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (f.commRingInverseImage.map α))).homEquiv _ _).symm
      ((differentialsIso f ψ).inv ≫ tensorInverseImageUnit f ψ α)

/-- The canonical forward and reverse tensor comparisons are mutually inverse. -/
private theorem tensorInverseImageIso_laws {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    tensorInverseImageIsoHom f ψ α ≫ tensorInverseImageIsoInv f ψ α = 𝟙 _ ∧
      tensorInverseImageIsoInv f ψ α ≫ tensorInverseImageIsoHom f ψ α = 𝟙 _ := by
  sorry

/-- Inverse image of a conormal tensor term, after coefficient transport to `f⁻¹Z`. -/
private def tensorInverseImageIso {X Y Z : Sheaf JC CommRingCat.{u}}
    (ψ : X ⟶ Y) (α : Y ⟶ Z) :
    (SheafOfModules.restrictScalars
        (f.commRingInverseImageForgetRingIso.app Z).hom).obj
      ((f.moduleInverseImage (ringSheaf JC Z)).obj ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap α)).obj
                                                      (relativeDifferentials ψ))) ≅
    (SheafOfModules.ChangeOfRings.extendScalars
      (ringSheafMap (f.commRingInverseImage.map α))).obj
        (relativeDifferentials (f.commRingInverseImage.map ψ)) where
  hom := tensorInverseImageIsoHom f ψ α
  inv := tensorInverseImageIsoInv f ψ α
  hom_inv_id := (tensorInverseImageIso_laws f ψ α).1
  inv_hom_id := (tensorInverseImageIso_laws f ψ α).2

/-- The pulled tensor term and the target tensor term are related by `standardTermIso`. -/
private theorem pulledAugmentation_comp_ringSheaf (φ : A ⟶ B) (n : ℕ) :
    ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)) =
      ringSheafMap (standardTermIso f φ n).hom.right ≫
        ringSheafMap
          (standardAugmentation (f.commRingInverseImage.obj A)
            (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)) :=
  sorry

/-- The inverse of `pulledAugmentation_comp_ringSheaf`. -/
private theorem pulledAugmentation_comp_ringSheaf_inv (φ : A ⟶ B) (n : ℕ) :
    ringSheafMap
      (standardAugmentation (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)) =
      ringSheafMap (standardTermIso f φ n).inv.right ≫
        ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)) :=
  sorry

/-- The canonical forward comparison of inverse-image tensor terms. -/
private def standardTermTensorHom (φ : A ⟶ B) (n : ℕ) :
    pulledTensor f φ n ⟶
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) :=
    ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))).homEquiv _ _).symm
      (RelativeDifferentials.map
          ⟨(Category.id_comp (targetTerm f φ (op ⦋n⦌)).hom).trans
            (standardTermIso f φ n).hom.w.symm⟩ ≫
        (restrictionAlong (standardTermIso f φ n).hom.right).map
          ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
              (ringSheafMap
                (standardAugmentation (f.commRingInverseImage.obj A)
                  (Under.mk (f.commRingInverseImage.map φ))
                  (op ⦋n⦌)))).unit.app
            (relativeDifferentials (targetTerm f φ (op ⦋n⦌)).hom)) ≫
          (SheafOfModules.Restriction.compIso'
              (ringSheafMap (standardTermIso f φ n).hom.right)
              (ringSheafMap
                (standardAugmentation (f.commRingInverseImage.obj A)
                  (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)))
              (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))
              (pulledAugmentation_comp_ringSheaf f φ n)).hom.app _)

/-- The canonical reverse comparison of inverse-image tensor terms. -/
private def standardTermTensorInv (φ : A ⟶ B) (n : ℕ) :
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) ⟶
    pulledTensor f φ n :=
    ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap
            (standardAugmentation (f.commRingInverseImage.obj A)
              (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)))).homEquiv _ _).symm
      (RelativeDifferentials.map
          ⟨(Category.id_comp (pulledTerm f φ (op ⦋n⦌)).hom).trans
            (standardTermIso f φ n).inv.w.symm⟩ ≫
        (restrictionAlong (standardTermIso f φ n).inv.right).map
          ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
              (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))).unit.app
            (relativeDifferentials (pulledTerm f φ (op ⦋n⦌)).hom)) ≫
          (SheafOfModules.Restriction.compIso'
              (ringSheafMap (standardTermIso f φ n).inv.right)
              (ringSheafMap (pulledAugmentation f φ (op ⦋n⦌)))
              (ringSheafMap
                (standardAugmentation (f.commRingInverseImage.obj A)
                  (Under.mk (f.commRingInverseImage.map φ)) (op ⦋n⦌)))
              (pulledAugmentation_comp_ringSheaf_inv f φ n)).hom.app _)

/-- The canonical forward and reverse tensor comparisons are mutually inverse. -/
private theorem standardTermTensorIso_laws (φ : A ⟶ B) (n : ℕ) :
    standardTermTensorHom f φ n ≫ standardTermTensorInv f φ n = 𝟙 _ ∧
      standardTermTensorInv f φ n ≫ standardTermTensorHom f φ n = 𝟙 _ := by
  sorry

/-- Degreewise comparison of pulled tensor terms with the tensor terms of `L(f⁻¹φ)`. -/
private def standardTermTensorIso (φ : A ⟶ B) (n : ℕ) :
    pulledTensor f φ n ≅
      (simplicialModule (f.commRingInverseImage.obj A)
        (Under.mk (f.commRingInverseImage.map φ))).obj (op ⦋n⦌) where
  hom := standardTermTensorHom f φ n
  inv := standardTermTensorInv f φ n
  hom_inv_id := (standardTermTensorIso_laws f φ n).1
  inv_hom_id := (standardTermTensorIso_laws f φ n).2

end

set_option backward.privateInPublic true in
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

/-- In strictly positive degrees, the zero comparisons of cotangent complexes compose
to the identities. -/
private theorem appIso_laws (φ : A ⟶ B) (k : ℕ) :
    (0 : (source f φ).X (Int.ofNat k.succ) ⟶ (target f φ).X (Int.ofNat k.succ)) ≫
      (0 : (target f φ).X (Int.ofNat k.succ) ⟶ (source f φ).X (Int.ofNat k.succ)) = 𝟙 _ ∧
    (0 : (target f φ).X (Int.ofNat k.succ) ⟶ (source f φ).X (Int.ofNat k.succ)) ≫
      (0 : (source f φ).X (Int.ofNat k.succ) ⟶ (target f φ).X (Int.ofNat k.succ)) = 𝟙 _ := by
  sorry

set_option backward.privateInPublic true in
/-- Degreewise comparison of the inverse-image and target cotangent complexes. -/
private def appIso (φ : A ⟶ B) :
    ∀ n : ℤ, (source f φ).X n ≅ (target f φ).X n
  | Int.ofNat (Nat.succ k) =>
      { hom := (0 : (source f φ).X (Int.ofNat k.succ) ⟶ (target f φ).X (Int.ofNat k.succ))
        inv := (0 : (target f φ).X (Int.ofNat k.succ) ⟶ (source f φ).X (Int.ofNat k.succ))
        hom_inv_id := (appIso_laws f φ k).1
        inv_hom_id := (appIso_laws f φ k).2 }
  | (0 : ℤ) =>
      (sourceXIso f φ 0).trans ((termIso f φ 0).trans (targetXIso f φ 0).symm)
  | Int.negSucc k =>
      (sourceXIso f φ k.succ).trans
        ((termIso f φ k.succ).trans (targetXIso f φ k.succ).symm)

set_option backward.privateInPublic true in
/-- The canonical identification `f⁻¹ L(φ) ≅ L(f⁻¹φ)` of cochain complexes of
`f⁻¹B`-modules. -/
def iso (φ : A ⟶ B) : source f φ ≅ target f φ :=
  HomologicalComplex.Hom.isoOfComponents (appIso f φ) (fun _ _ _ ↦ sorry)

/-- In cohomological degree `-n`, the comparison is the inverse-image comparison of
simplicial tensor terms. -/
theorem iso_hom_f (φ : A ⟶ B) (n : ℕ) :
    (iso f φ).hom.f (-n) =
      (sourceXIso f φ n).hom ≫ (termIso f φ n).hom ≫ (targetXIso f φ n).inv :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex.InverseImage
