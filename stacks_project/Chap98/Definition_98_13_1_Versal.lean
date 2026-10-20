/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.«98_3_1_1_Functor»

/-!
# Versality at a finite type point

Compatibility checks for the canonical pointwise versality API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidsOver.yonedaOfObject :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU),
    GroupoidsOver.slice (Over.mk hU) ⟶ X)

#check (AlgebraicGeometry.GroupoidsOver.yonedaOfObject_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU),
    yonedaOfObject hU x hx = YonedaSlice.representative ⟨x, hx⟩)

#check (AlgebraicGeometry.GroupoidsOver.sliceIdentityObject :
  ∀ {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S),
    (GroupoidsOver.slice (Over.mk hU)).total)

#check (AlgebraicGeometry.GroupoidsOver.sliceIdentityObject_over :
  ∀ {S : Scheme.{u}} {U : Scheme.{u}}
    (hU : U ⟶ S),
    (GroupoidsOver.slice (Over.mk hU)).p.obj (sliceIdentityObject hU) =
      Over.mk hU)

#check (AlgebraicGeometry.GroupoidsOver.residueFieldType :
  ∀ {U : Scheme.{u}} (u0 : U),
    Type u)

#check (AlgebraicGeometry.GroupoidsOver.residueFieldType_spec :
  ∀ {U : Scheme.{u}} (u0 : U),
    CommRingCat.of (residueFieldType u0) = U.residueField u0)

#check (AlgebraicGeometry.GroupoidsOver.fromResidueField :
  ∀ {U : Scheme.{u}} (u0 : U),
    Spec (CommRingCat.of (residueFieldType u0)) ⟶ U)

#check (AlgebraicGeometry.GroupoidsOver.fromResidueField_eq :
  ∀ {U : Scheme.{u}} (u0 : U),
    fromResidueField u0 = U.fromSpecResidueField u0)

#check (AlgebraicGeometry.GroupoidsOver.residueSliceObject :
  ∀ {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S) (u0 : U),
    (GroupoidsOver.slice (Over.mk hU)).p.Fiber
      (Over.mk (fromResidueField u0 ≫ hU)))

#check (AlgebraicGeometry.GroupoidsOver.residueSliceObject_spec :
  ∀ {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)
    (u0 : U),
    Functor.Fiber.fiberInclusion.obj (residueSliceObject hU u0) =
      Over.mk (Over.homMk (fromResidueField u0)
        rfl : Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU))

#check (AlgebraicGeometry.GroupoidsOver.instLocallyOfFiniteType_residuePoint :
  ∀ {S : Scheme.{u}} {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0],
    LocallyOfFiniteType (fromResidueField u0 ≫ hU))

#check (AlgebraicGeometry.GroupoidsOver.hat :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU),
    Predeformation.predeformation openImmersion h_factor
        (GroupoidsOver.slice (Over.mk hU)) (residueSliceObject hU u0) ⥤ᵇ
      Predeformation.predeformation openImmersion h_factor X
        (Predeformation.residueImage (yonedaOfObject hU x hx)
          (residueSliceObject hU u0)))

#check (AlgebraicGeometry.GroupoidsOver.hat_spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU),
    hat hU x hx u0 openImmersion h_factor =
      Predeformation.map openImmersion h_factor (yonedaOfObject hU x hx)
        (residueSliceObject hU u0))

#check (AlgebraicGeometry.GroupoidsOver.instIsFiberedInGroupoidsOp_predeformation :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u} [CommRing Λ]
    [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS)),
    Functor.IsFibered.InGroupoids
      (Predeformation.predeformation openImmersion h_factor X x0).p.op)

#check (AlgebraicGeometry.GroupoidsOver.IsVersalAt :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.IsVersalAt.sliceId :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0],
    IsVersalAt hU (sliceIdentityObject hU) (sliceIdentityObject_over hU) u0)

#check (AlgebraicGeometry.GroupoidsOver.IsVersalAt.spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU),
    BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor))

#check (AlgebraicGeometry.GroupoidsOver.IsVersalAt.iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor))

namespace AlgebraicGeometry.GroupoidsOver

/-- Versality at a finite type point is smoothness of the canonical residue-field
`hat` functor on every affine-open factorization over the base scheme. -/
theorem isVersalAt_iff {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor) :=
  AlgebraicGeometry.GroupoidsOver.IsVersalAt.iff hU x hx u0

end AlgebraicGeometry.GroupoidsOver
