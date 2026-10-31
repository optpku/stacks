/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Equivalence
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.RingTheory.Algebra.TensorProduct.BaseChange

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The polynomial map defined by the presentation's variable images and the new coefficients.
This map is defined for any `f`; surjectivity requires `f` to be the actual `R`-algebra map. -/
noncomputable def baseChangeMap {f : R →+* A} (p : Presentation f)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    MvPolynomial (Fin p.n) R' →+* A ⊗[R] R' :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] A ⊗[R] R').toRingHom
    (fun i : Fin p.n ↦
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R') (p.map (MvPolynomial.X i)))

/-- The coefficient extension of a presentation map restricts to the induced structure map. -/
theorem baseChangeMap_comp_C {f : R →+* A} (p : Presentation f)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.baseChangeMap R').comp MvPolynomial.C = algebraMap R' (A ⊗[R] R') := sorry

/-- Coefficient extension preserves surjectivity of a presentation of the actual algebra map. -/
theorem baseChangeMap_surjective (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Function.Surjective (p.baseChangeMap R') := sorry

/-- The finite polynomial presentation induced after base change along `R → R'`. -/
noncomputable def baseChange (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Presentation (algebraMap R' (A ⊗[R] R')) :=
  Presentation.ofSurjection (algebraMap R' (A ⊗[R] R')) p.n (p.baseChangeMap R')
    (p.baseChangeMap_comp_C R') (p.baseChangeMap_surjective R')

/-- The base-changed presentation has the same number of polynomial variables. -/
theorem baseChange_n (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.baseChange R').n = p.n := sorry

/-- The map of the base-changed presentation is the coefficient-extended presentation map. -/
theorem baseChange_map (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.baseChange R').map = p.baseChangeMap R' := sorry

section Comparison

variable (p : Presentation (algebraMap R A))

-- Local instance justification (noncanonical choice): the chosen presentation `p` determines the intermediate polynomial-algebra structure on `A`.
local instance presentationAlgebra : Algebra (MvPolynomial (Fin p.n) R) A :=
  p.map.toAlgebra

-- Local instance justification (noncanonical choice): `p.map_comp` determines scalar-tower compatibility for the chosen presentation.
local instance presentationScalarTower :
    IsScalarTower R (MvPolynomial (Fin p.n) R) A :=
  IsScalarTower.of_algebraMap_eq' p.map_comp.symm

/-- The polynomial extension occurring in base change is Tor independent of the presentation
target whenever the original two algebras are Tor independent over `R`. -/
theorem polynomialTorIndependent
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    Tor.IsIndependent
      (ModuleCat.of (MvPolynomial (Fin p.n) R) A)
      (ModuleCat.of (MvPolynomial (Fin p.n) R)
        (R' ⊗[R] MvPolynomial (Fin p.n) R)) := sorry

/-- The polynomial/tensor equivalence used to compare the two coefficient-extension routes. -/
noncomputable def baseChangePolynomialEquiv
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    R' ⊗[R] MvPolynomial (Fin p.n) R ≃+* MvPolynomial (Fin p.n) R' :=
  (MvPolynomial.algebraTensorAlgEquiv R R').toRingEquiv

/-- The iterated tensor-product target of the presentation is canonically the base-changed
target ring `A ⊗[R] R'`. -/
noncomputable def torBaseChangeTargetEquiv
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A) ≃+*
      A ⊗[R] R' :=
  (Algebra.TensorProduct.baseChangeRight :
      (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A ≃+*
        R' ⊗[R] A).trans
    (Algebra.TensorProduct.comm R R' A).toRingEquiv

/-- The target equivalence carries the presentation-induced map from `A` to the canonical map
`A → A ⊗[R] R'`. -/
theorem baseChangeTargetEquiv_comp_includeRight
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.torBaseChangeTargetEquiv R').toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          A →ₐ[MvPolynomial (Fin p.n) R]
            (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R').toRingHom := sorry

/-- The target and polynomial equivalences identify the iterated tensor presentation map with
the coefficient-extended presentation map. -/
theorem baseChangeSquare
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.torBaseChangeTargetEquiv R').toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
            (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom =
      (p.baseChangeMap R').comp (p.baseChangePolynomialEquiv R').toRingHom := sorry

/-- The polynomial/tensor equivalence identifies the two composite coefficient maps from `R`. -/
theorem baseChangePolynomialEquiv_comp
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (p.baseChangePolynomialEquiv R').toRingHom.comp
        ((Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin p.n) R →ₐ[R]
            R' ⊗[R] MvPolynomial (Fin p.n) R).toRingHom.comp MvPolynomial.C) =
      (MvPolynomial.C : R' →+* MvPolynomial (Fin p.n) R').comp (algebraMap R R') := sorry

/-- Derived extension along the canonical target-ring equivalence, with the source and target
ring structures fixed explicitly. -/
noncomputable abbrev targetExtension
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    DerivedCategory
        (@ModuleCat.{u, u}
          ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
          CommRing.toRing) ⥤
      DerivedCategory (@ModuleCat.{u, u} (A ⊗[R] R') CommRing.toRing) :=
  @derivedExtensionOfScalars.{u, u, u}
    ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
    (A ⊗[R] R') inferInstance inferInstance
    (p.torBaseChangeTargetEquiv R').toRingHom inferInstance

/-- Extension along the polynomial-coordinate equivalence followed by coextension is direct
coextension along the composite map. -/
noncomputable def polynomialCoordinateChangeIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedExtensionOfScalars (p.baseChangePolynomialEquiv R').toRingHom ⋙
        derivedCoextensionOfScalars (p.baseChangeMap R') ≅
      derivedCoextensionOfScalars
        ((p.baseChangeMap R').comp (p.baseChangePolynomialEquiv R').toRingHom) :=
  Functor.isoWhiskerRight
      (derivedExtensionIsoRestrictionOfRingEquiv (p.baseChangePolynomialEquiv R'))
      (derivedCoextensionOfScalars (p.baseChangeMap R')) ≪≫
    Functor.isoWhiskerRight
      (derivedCoextensionIsoRestrictionOfRingEquiv (p.baseChangePolynomialEquiv R')).symm
      (derivedCoextensionOfScalars (p.baseChangeMap R')) ≪≫
    DerivedCoextension.compIso (p.baseChangePolynomialEquiv R').toRingHom
      (p.baseChangeMap R')

/-- Direct coextension along the transported target map agrees with iterated coextension. -/
noncomputable def targetCoextensionCompIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedCoextensionOfScalars
        ((p.torBaseChangeTargetEquiv R').toRingHom.comp
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom) ≅
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        @derivedCoextensionOfScalars
          ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
          (A ⊗[R] R') inferInstance inferInstance
          (p.torBaseChangeTargetEquiv R').toRingHom :=
  (DerivedCoextension.compIso
      (Algebra.TensorProduct.includeLeft :
        (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
          (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom
      (p.torBaseChangeTargetEquiv R').toRingHom).symm

/-- Iterated coextension along the target equivalence agrees with restriction along its
inverse after coextension from the polynomial tensor product. -/
noncomputable def targetCoextensionRestrictionIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        @derivedCoextensionOfScalars
          ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
          (A ⊗[R] R') inferInstance inferInstance
          (p.torBaseChangeTargetEquiv R').toRingHom ≅
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        @derivedRestrictionOfScalars (A ⊗[R] R')
          ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
          inferInstance inferInstance (p.torBaseChangeTargetEquiv R').symm.toRingHom :=
  Functor.isoWhiskerLeft
      (derivedCoextensionOfScalars
        (Algebra.TensorProduct.includeLeft :
          (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
            (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom)
      (derivedCoextensionIsoRestrictionOfRingEquiv (p.torBaseChangeTargetEquiv R'))

/-- Restriction along the inverse target equivalence agrees with extension along the target
equivalence after coextension from the polynomial tensor product. -/
noncomputable def targetRestrictionExtensionIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        @derivedRestrictionOfScalars (A ⊗[R] R')
          ((R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A)
          inferInstance inferInstance (p.torBaseChangeTargetEquiv R').symm.toRingHom ≅
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        targetExtension p R' :=
  Functor.isoWhiskerLeft
      (derivedCoextensionOfScalars
        (Algebra.TensorProduct.includeLeft :
          (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
            (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom)
      (derivedExtensionIsoRestrictionOfRingEquiv (p.torBaseChangeTargetEquiv R')).symm

/-- Coextension along the transported target map agrees with coextension followed by
extension along the target-ring equivalence. -/
noncomputable def targetCoordinateChangeIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedCoextensionOfScalars
        ((p.torBaseChangeTargetEquiv R').toRingHom.comp
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom) ≅
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        targetExtension p R' :=
  p.targetCoextensionCompIso R' ≪≫
    p.targetCoextensionRestrictionIso R' ≪≫
    p.targetRestrictionExtensionIso R'

/-- Extension followed by coextension is unchanged by the compatible polynomial and target
ring equivalences in the base-change square. -/
noncomputable def coordinateChangeIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedExtensionOfScalars (p.baseChangePolynomialEquiv R').toRingHom ⋙
        derivedCoextensionOfScalars (p.baseChangeMap R') ≅
      derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            (R' ⊗[R] MvPolynomial (Fin p.n) R) →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom ⋙
        targetExtension p R' :=
  p.polynomialCoordinateChangeIso R' ≪≫
    eqToIso (congrArg derivedCoextensionOfScalars (p.baseChangeSquare R').symm) ≪≫
    p.targetCoordinateChangeIso R'

/-- The two iterated polynomial scalar-extension routes agree after the canonical
polynomial/tensor identification. -/
noncomputable def polynomialExtensionIso
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    derivedExtensionOfScalars
          (MvPolynomial.C : R →+* MvPolynomial (Fin p.n) R) ⋙
        derivedExtensionOfScalars
          (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin p.n) R →ₐ[R]
              R' ⊗[R] MvPolynomial (Fin p.n) R).toRingHom ⋙
        derivedExtensionOfScalars (p.baseChangePolynomialEquiv R').toRingHom ≅
      derivedExtensionOfScalars (algebraMap R R') ⋙
        derivedExtensionOfScalars
          (MvPolynomial.C : R' →+* MvPolynomial (Fin p.n) R') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight
      (DerivedExtension.Composition.iso
        (MvPolynomial.C : R →+* MvPolynomial (Fin p.n) R)
        (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin p.n) R →ₐ[R]
            R' ⊗[R] MvPolynomial (Fin p.n) R).toRingHom)
      (derivedExtensionOfScalars (p.baseChangePolynomialEquiv R').toRingHom) ≪≫
    DerivedExtension.Composition.iso
      ((Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin p.n) R →ₐ[R]
          R' ⊗[R] MvPolynomial (Fin p.n) R).toRingHom.comp MvPolynomial.C)
      (p.baseChangePolynomialEquiv R').toRingHom ≪≫
    eqToIso (congrArg (fun f ↦ derivedExtensionOfScalars f)
      (p.baseChangePolynomialEquiv_comp R')) ≪≫
    (DerivedExtension.Composition.iso (algebraMap R R')
      (MvPolynomial.C : R' →+* MvPolynomial (Fin p.n) R')).symm

/-- The component of the canonical comparison between direct target extension and extension
through the presentation-induced tensor-product target. -/
noncomputable def targetExtensionComparisonApp
    (R' : Type u) [CommRing R'] [Algebra R R']
    (M : DerivedCategory (ModuleCat A)) :
    (derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj M ⟶
      (targetExtension p R').obj
        ((derivedExtensionOfScalars
          (Algebra.TensorProduct.includeRight :
            A →ₐ[MvPolynomial (Fin p.n) R]
              (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom).obj M) :=
  (derivedExtensionOfScalarsCompIso
    (Algebra.TensorProduct.includeRight :
      A →ₐ[MvPolynomial (Fin p.n) R]
        (R' ⊗[R] MvPolynomial (Fin p.n) R) ⊗[MvPolynomial (Fin p.n) R] A).toRingHom
    (p.torBaseChangeTargetEquiv R').toRingHom
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R').toRingHom
    (p.baseChangeTargetEquiv_comp_includeRight R')).inv.app M

/-- The explicit component of the upper-shriek base-change comparison. -/
noncomputable def baseChangeComparisonApp
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R'))
    (K : DerivedCategory (ModuleCat R)) :
    (derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj (p.functor.obj K) ⟶
      (p.baseChange R').functor.obj
        ((derivedExtensionOfScalars (algebraMap R R')).obj K) :=
  let P := MvPolynomial (Fin p.n) R
  let P₀ := R' ⊗[R] P
  let B₀ := P₀ ⊗[P] A
  let X := (derivedExtensionOfScalars (MvPolynomial.C : R →+* P)).obj K
  let Z := (derivedExtensionOfScalars
    (Algebra.TensorProduct.includeRight : P →ₐ[R] P₀).toRingHom).obj X
  let extendToTarget : DerivedCategory (ModuleCat B₀) ⥤
      DerivedCategory (ModuleCat (A ⊗[R] R')) := targetExtension p R'
  let extendFromA : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat B₀) :=
    derivedExtensionOfScalars
      (Algebra.TensorProduct.includeRight : A →ₐ[P] B₀).toRingHom
  let coextendFromP₀ : DerivedCategory (ModuleCat P₀) ⥤
      DerivedCategory (ModuleCat B₀) :=
    derivedCoextensionOfScalars
      (Algebra.TensorProduct.includeLeft : P₀ →ₐ[P] B₀).toRingHom
  let shiftB₀ := shiftFunctor (DerivedCategory (ModuleCat B₀)) (p.n : ℤ)
  let shiftTarget :=
    shiftFunctor (DerivedCategory (ModuleCat (A ⊗[R] R'))) (p.n : ℤ)
  let compareExtension :
      (derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj (p.functor.obj K) ⟶
        extendToTarget.obj (extendFromA.obj (p.functor.obj K)) :=
    p.targetExtensionComparisonApp R' (p.functor.obj K)
  let compareDuality : extendToTarget.obj (extendFromA.obj (p.functor.obj K)) ⟶
      extendToTarget.obj (shiftB₀.obj (coextendFromP₀.obj Z)) :=
    extendToTarget.map
      (((derivedExtensionOfScalars
          (Algebra.TensorProduct.includeRight : A →ₐ[P] B₀).toRingHom).commShiftIso
        (p.n : ℤ)).hom.app
          ((derivedCoextensionOfScalars p.map).obj X) ≫
        shiftB₀.map (trivialDualityBaseChangeMap X (p.polynomialTorIndependent R' hTor)))
  let compareShift : extendToTarget.obj (shiftB₀.obj (coextendFromP₀.obj Z)) ⟶
      shiftTarget.obj (extendToTarget.obj (coextendFromP₀.obj Z)) :=
    ((targetExtension p R').commShiftIso (p.n : ℤ)).hom.app (coextendFromP₀.obj Z)
  let compareCoordinates : extendToTarget.obj (coextendFromP₀.obj Z) ⟶
      (derivedCoextensionOfScalars (p.baseChangeMap R')).obj
        ((derivedExtensionOfScalars
          (MvPolynomial.C : R' →+* MvPolynomial (Fin p.n) R')).obj
            ((derivedExtensionOfScalars (algebraMap R R')).obj K)) :=
    (coordinateChangeIso p R').inv.app Z ≫
        (derivedCoextensionOfScalars (p.baseChangeMap R')).map
          ((polynomialExtensionIso p R').hom.app K)
  compareExtension ≫ compareDuality ≫ compareShift ≫ shiftTarget.map compareCoordinates

/-- The functorial upper-shriek base-change comparison attached to a chosen presentation. -/
noncomputable def baseChangeComparison
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    p.functor ⋙ derivedExtensionOfScalars (algebraMap A (A ⊗[R] R')) ⟶
      derivedExtensionOfScalars (algebraMap R R') ⋙ (p.baseChange R').functor where
  app := p.baseChangeComparisonApp R' hTor
  naturality _ _ _ := sorry

/-- Evaluation of the functorial comparison is the explicit component construction. -/
theorem baseChangeComparison_app
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R'))
    (K : DerivedCategory (ModuleCat R)) :
    (p.baseChangeComparison R' hTor).app K = p.baseChangeComparisonApp R' hTor K := sorry

end Comparison

/-- The upper-shriek base-change comparison for a flat coefficient extension. -/
noncomputable def flatBaseChange
    (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    p.functor ⋙ derivedExtensionOfScalars (algebraMap A (A ⊗[R] R')) ⟶
      derivedExtensionOfScalars (algebraMap R R') ⋙ (p.baseChange R').functor :=
  p.baseChangeComparison R' Tor.IsIndependent.of_flat_right

/-- For Noetherian rings, every bounded-below component of the flat upper-shriek
base-change comparison is an isomorphism. -/
theorem flatBaseChange_app_isIso_of_boundedBelow
    [IsNoetherianRing R]
    (p : Presentation (algebraMap R A))
    (R' : Type u) [CommRing R'] [Algebra R R']
    [IsNoetherianRing R'] [Module.Flat R R']
    (K : DerivedCategory (ModuleCat.{u, u} R)) (hK : ∃ n : ℤ, K.IsGE n) :
    IsIso ((p.flatBaseChange R').app K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
