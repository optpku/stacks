/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.Algebra.Module.ULift
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The multiplicity-vector map from the integers to the indexed special-fibre components. -/
noncomputable def firstMap
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Scheme.Hom.FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    ℤ →ₗ[ℤ] (Fin n → ℤ) :=
  LinearMap.smulRight (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    (fun i ↦ (f.specialFiberMultiplicities (components i) : ℤ))

/-- The linear map sending a component coefficient vector to its Picard class. -/
noncomputable def componentPicardMap
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (Fin n → ℤ) →ₗ[ℤ] X.PicardGroup :=
  Fintype.linearCombination ℤ (fun i ↦
    Scheme.Modules.picardClass (f.specialFiberComponent (components i)).associatedSheaf)

/-- The Picard-group homomorphism induced by restriction to a chosen generic fibre. -/
noncomputable def genericFiberPicardRestriction
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    X.PicardGroup →+ C.left.PicardGroup :=
  Scheme.Hom.picardPullback
    (genericFiberIso.hom.left ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- The five-arrow additive-group row for the Picard sequence of a regular model. -/
noncomputable def picardSequence
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    ComposableArrows AddCommGrpCat.{u + 1} 5 :=
  let firstMapLift : ULift.{u + 1} ℤ →ₗ[ℤ] ULift.{u + 1} (Fin n → ℤ) :=
    (LinearMap.ulift (firstMap f n components) :
      ULift.{u + 1} ℤ →ₗ[ℤ] ULift.{u + 1} (Fin n → ℤ))
  let componentPicardMapLift : ULift.{u + 1} (Fin n → ℤ) →ₗ[ℤ] X.PicardGroup :=
    (ULift.moduleEquiv : ULift.{0} X.PicardGroup ≃ₗ[ℤ] X.PicardGroup).toLinearMap.comp
      (LinearMap.ulift (componentPicardMap f n components) :
        ULift.{u + 1} (Fin n → ℤ) →ₗ[ℤ] ULift.{0} X.PicardGroup)
  ComposableArrows.mk₅
    (0 : (⊥_ AddCommGrpCat.{u + 1}) ⟶ AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (AddCommGrpCat.ofHom firstMapLift.toAddMonoidHom)
    (AddCommGrpCat.ofHom componentPicardMapLift.toAddMonoidHom)
    (AddCommGrpCat.ofHom (genericFiberPicardRestriction f genericFiberIso))
    (0 : AddCommGrpCat.of C.left.PicardGroup ⟶ ⊥_ AddCommGrpCat.{u + 1})

/-- For a proper flat regular model of a smooth projective curve over a discrete valuation ring, when the generic curve has only constant global functions, the associated Picard sequence is exact. -/
theorem picardSequence_exact
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (picardSequence C f genericFiberIso n components).Exact := sorry

/-- The first map sends `1` to the special-fibre multiplicity vector. -/
theorem picardSequence_firstMap_one
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    firstMap f n components 1 =
      (fun i ↦ (f.specialFiberMultiplicities (components i) : ℤ)) := sorry

/-- The component map sends each coordinate basis vector to the corresponding component class. -/
theorem picardSequence_componentMap_basis
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    componentPicardMap f n components (Pi.single i 1) =
      Scheme.Modules.picardClass
        (f.specialFiberComponent (components i)).associatedSheaf := sorry

/- Exposed additive-group consequences of the five-arrow Picard sequence. -/

/-- The component-divisor map and generic-fibre restriction are exact at the model Picard group. -/
theorem componentPicardMap_exact
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Function.Exact (componentPicardMap f n components)
      (genericFiberPicardRestriction f genericFiberIso) := sorry

/-- The generic-fibre restriction map in the Picard sequence is surjective. -/
theorem genericFiberPicardRestriction_surjective
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Function.Surjective (genericFiberPicardRestriction f genericFiberIso) := sorry

end AlgebraicGeometry.Scheme.Hom
