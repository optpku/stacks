/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology comparison for derived extension of scalars

The unit of the derived extension-restriction adjunction induces a canonical comparison from
extension of the homology of a derived complex to the homology of its derived scalar extension.
Composing this comparison with a map out of the derived scalar extension gives the corresponding
base-change map on homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape
open scoped TensorProduct

universe u v

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Derived restriction of scalars commutes canonically with homology. -/
@[stacks 0GMT "derived restriction commutes with homology"]
noncomputable def derivedRestrictionHomologyIso
    (σ : R →+* S) (L : DerivedCategory (ModuleCat.{max u v, u} S)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).obj
        ((derivedRestrictionOfScalars σ).obj L) ≅
      (ModuleCat.restrictScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).obj K
  let eS :
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v, u} S) i).app K
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).mapIso
      ((((derivedRestrictionOfScalars σ).mapIso
        (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v, u} R) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars σ) ≪≫
      (ModuleCat.restrictScalars σ).mapIso eS.symm

/-- Homology of the adjunction transpose of a map out of derived extension of scalars. -/
noncomputable def homologyUntranspose (σ : R →+* S)
    {K : DerivedCategory (ModuleCat.{max u v, u} R)}
    {L : DerivedCategory (ModuleCat.{max u v, u} S)}
    (α : (derivedExtensionOfScalars σ).obj K ⟶ L) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).obj K ⟶
      (ModuleCat.restrictScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).obj L) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).map
      ((derivedExtensionRestrictionAdjunction σ).homEquiv K L α) ≫
    (derivedRestrictionHomologyIso σ L i).hom

/-- The adjoint-side map obtained by applying homology to the unit of the derived
extension-restriction adjunction. -/
@[stacks 0GMT "adjoint derived-extension homology comparison"]
noncomputable abbrev derivedExtensionHomologyComparisonAdjoint
    (σ : R →+* S) (K : DerivedCategory (ModuleCat.{max u v, u} R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).obj K ⟶
      (ModuleCat.restrictScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).obj
          ((derivedExtensionOfScalars σ).obj K)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).map
      ((derivedExtensionRestrictionAdjunction σ).unit.app K) ≫
    (derivedRestrictionHomologyIso σ ((derivedExtensionOfScalars σ).obj K) i).hom

/-- The homology comparison from extension of homology to homology after derived extension of
scalars, obtained by transposing `derivedExtensionHomologyComparisonAdjoint`. -/
@[stacks 0GMT "derived-extension homology comparison"]
noncomputable def derivedExtensionHomologyComparison
    (σ : R →+* S) (K : DerivedCategory (ModuleCat.{max u v, u} R)) (i : ℤ) :
    (ModuleCat.extendScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} R) i).obj K) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} S) i).obj
        ((derivedExtensionOfScalars σ).obj K) :=
  ((ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} σ).homEquiv _ _).symm
    (derivedExtensionHomologyComparisonAdjoint σ K i)

/-- The cohomology base-change morphism obtained by first comparing extension of cohomology
with cohomology after derived extension, then applying cohomology to the given derived map.

Here `A ⊗[R] R'` is the scalar-extension ring, `A'` is the target ring, and `KBase` is a
derived object carrying its canonical `A ⊗[R] R'`-module structure. -/
noncomputable def cohomologyBaseChangeMap
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] (σ : (A ⊗[R] R') →+* A')
    (KBase : DerivedCategory (ModuleCat.{max u v, u} (A ⊗[R] R')))
    (K' : DerivedCategory (ModuleCat.{max u v, u} A'))
    (α : (derivedExtensionOfScalars σ).obj KBase ⟶ K') (i : ℤ) :
    (ModuleCat.extendScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} (A ⊗[R] R')) i).obj KBase) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} A') i).obj K' :=
  derivedExtensionHomologyComparison σ KBase i ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} A') i).map α

/-- The cohomology base-change map is the scalar-extension comparison followed by the
cohomology map induced by the given derived morphism. -/
theorem cohomologyBaseChangeMap_eq
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] (σ : (A ⊗[R] R') →+* A')
    (KBase : DerivedCategory (ModuleCat.{max u v, u} (A ⊗[R] R')))
    (K' : DerivedCategory (ModuleCat.{max u v, u} A'))
    (α : (derivedExtensionOfScalars σ).obj KBase ⟶ K') (i : ℤ) :
    cohomologyBaseChangeMap σ KBase K' α i =
      derivedExtensionHomologyComparison σ KBase i ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v, u} A') i).map α := sorry

end CategoryTheory.ModuleCat
