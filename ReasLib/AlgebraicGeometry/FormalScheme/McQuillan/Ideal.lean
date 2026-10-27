/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Basic
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan

/-!
# Weak ideals of definition on McQuillan formal schemes

An ideal sheaf on a McQuillan formal scheme is determined by its values on
formal affine opens, with the restriction-compatibility of an ideal sheaf.
It is a weak ideal of definition when those values are weak ideals of
definition of the weakly admissible section rings.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- Affine formal opens of a McQuillan formal scheme have weakly admissible
section rings. -/
instance instIsWeaklyAdmissibleRing_sections {X : FormalScheme.{u}}
    (U : X.affineOpens) :
    IsWeaklyAdmissibleRing (X.presheaf.obj (op U.1) : Type u) :=
  sorry

/-- An ideal sheaf on a McQuillan formal scheme, recorded by its ideals of
sections on formal affine opens, restriction closure, and local membership descent.
No algebraic localization equality is imposed: formal affine sections are inverse limits. -/
structure IdealSheafData (X : FormalScheme.{u}) where
  /-- The component of the ideal sheaf at a formal affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u)
  /-- Restriction carries ideal sections into ideal sections. -/
  map_ideal :
    ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
      (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U

  /-- Membership descends along affine covers of an affine open. -/
  local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
    (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
    (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
    (f : (X.presheaf.obj (op U.1) : Type u)),
    (∀ (V : X.affineOpens) (hV : 𝒰 V),
      (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U

/-- Construct ideal-sheaf data from an affine-open family of ideals together
with the restriction-compatibility of an ideal sheaf. -/
def IdealSheafData.of {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U)
    (local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
      (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
      (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
      (f : (X.presheaf.obj (op U.1) : Type u)),
      (∀ (V : X.affineOpens) (hV : 𝒰 V),
        (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U) :
    IdealSheafData X where
  ideal := ideal
  map_ideal := map_ideal
  local_mem := local_mem

/-- The smart constructor recovers the given affine-open family of ideals. -/
theorem IdealSheafData.of_spec {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U)
    (local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
      (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
      (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
      (f : (X.presheaf.obj (op U.1) : Type u)),
      (∀ (V : X.affineOpens) (hV : 𝒰 V),
        (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U) :
    (IdealSheafData.of ideal map_ideal local_mem).ideal = ideal :=
  rfl

/-- Restriction compatibility of an ideal sheaf on formal affine opens. -/
theorem IdealSheafData.map_ideal_apply {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ I.ideal U :=
  I.map_ideal h

/-- Ideal-sheaf data are determined by their affine section ideals. -/
@[ext] theorem IdealSheafData.ext {X : FormalScheme.{u}} {I J : IdealSheafData X}
    (h : I.ideal = J.ideal) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The kernel ideal sheaf of a morphism, computed from its actual structure-sheaf map.
Local membership descent uses the sheaf condition on the source, with no affine
localization assumption on either formal scheme. -/
def Hom.ker {Y X : FormalScheme.{u}} (f : Y ⟶ X) : IdealSheafData X where
  ideal U := RingHom.ker ((Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val
  map_ideal := by
    intro U V h
    apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    change ((Hom.toLTRSHom f).toSheafedHom.hom.c.app (op V.1)).val s = 0 at hs
    change (X.presheaf.map (homOfLE h).op ≫
      (Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val s = 0
    have hnat := congrArg (fun g ↦ g.val s)
      ((Hom.toLTRSHom f).toSheafedHom.hom.c.naturality (homOfLE h).op)
    exact hnat.trans (by
      change (((Hom.toLTRSHom f).toSheafedHom.hom.base _* Y.presheaf).map
        (homOfLE h).op).val
          (((Hom.toLTRSHom f).toSheafedHom.hom.c.app (op V.1)).val s) = 0
      rw [hs]
      exact map_zero (((Hom.toLTRSHom f).toSheafedHom.hom.base _* Y.presheaf).map
        (homOfLE h).op).val)
  local_mem := by
    sorry

/-- The affine sections of the kernel sheaf are the sectionwise kernels. -/
theorem Hom.ker_ideal {Y X : FormalScheme.{u}} (f : Y ⟶ X) (U : X.affineOpens) :
    (Hom.ker f).ideal U =
      RingHom.ker ((Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val :=
  rfl

/-- The ideal of sections over an arbitrary open, obtained by comapping the
affine-open components along restriction. -/
def IdealSheafData.idealOn {X : FormalScheme.{u}} (I : IdealSheafData X)
    (U : Opens X.carrier) : Ideal (X.presheaf.obj (op U) : Type u) :=
  ⨅ (V : X.affineOpens), ⨅ (hVU : V.1 ≤ U),
    (I.ideal V).comap (X.presheaf.map (homOfLE hVU).op).val

/-- Membership in `idealOn` is restriction into every affine-open component. -/
theorem IdealSheafData.mem_idealOn {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U : Opens X.carrier} {f : (X.presheaf.obj (op U) : Type u)} :
    f ∈ I.idealOn U ↔
      ∀ (V : X.affineOpens) (h : V.1 ≤ U),
        (X.presheaf.map (homOfLE h).op).val f ∈ I.ideal V :=
  by simp only [IdealSheafData.idealOn, Submodule.mem_iInf, Ideal.mem_comap]

/-- On a formal affine open, `idealOn` recovers the component ideal. -/
theorem IdealSheafData.idealOn_affine {X : FormalScheme.{u}} (I : IdealSheafData X)
    (U : X.affineOpens) :
    I.idealOn U.1 = I.ideal U :=
  by
    apply le_antisymm
    · intro f hf
      have hf' := (I.mem_idealOn.mp hf) U le_rfl
      change (X.presheaf.map (𝟙 (op U.1))).val f ∈ I.ideal U at hf'
      rw [X.presheaf.map_id] at hf'
      exact hf'
    · intro f hf
      exact I.mem_idealOn.mpr fun V h ↦
        I.map_ideal h (Ideal.mem_map_of_mem _ hf)

/-- The ideals on arbitrary opens satisfy local membership descent, hence define
an ideal subsheaf rather than only a subpresheaf. -/
theorem IdealSheafData.idealOn_local_mem {X : FormalScheme.{u}} (I : IdealSheafData X)
    (U : Opens X.carrier) (𝒰 : Opens X.carrier → Prop)
    (hle : ∀ V, 𝒰 V → V ≤ U)
    (hcover : ⨆ (V : Opens X.carrier) (_ : 𝒰 V), V = U)
    (f : (X.presheaf.obj (op U) : Type u))
    (hf : ∀ (V : Opens X.carrier) (hV : 𝒰 V),
      (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ I.idealOn V) :
    f ∈ I.idealOn U :=
  sorry

/-- Evaluation of inverse-limit sections at a weak quotient. -/
def IdealSheafData.spfQuotientProjection (A : TopCommRingCat.{u})
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (I : Ideal (A : Type u)) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (U : Opens T) :
    FormalSpectrum.Sections e U →+* FormalSpectrum.componentType e U I hI where
  toFun s := s.component I hI
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The quotient projection evaluates a compatible section family at its `I` component. -/
theorem IdealSheafData.spfQuotientProjection_apply (A : TopCommRingCat.{u})
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (I : Ideal (A : Type u)) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (U : Opens T) (s : FormalSpectrum.Sections e U) :
    IdealSheafData.spfQuotientProjection A e I hI U s = s.component I hI :=
  rfl

/-- A weak open ideal gives the kernel of the quotient-sheaf projection on `Spf(A)`.
On smaller affines this is a kernel of inverse-limit sections, not algebraic extension. -/
def IdealSheafData.ofSpfOnSpace (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (I : Ideal (A : Type u)) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    IdealSheafData (FormalScheme.ofSpfOnSpace A hA e) where
  ideal U := RingHom.ker (IdealSheafData.spfQuotientProjection A e I hI U.1)
  map_ideal := by
    intro U V h
    apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    change s.component I hI = 0 at hs
    change FormalSpectrum.componentRestrict e h I hI (s.component I hI) = 0
    rw [hs, map_zero]
  local_mem := by
    sorry

/-- The affine component of `ofSpfOnSpace` is the actual quotient-projection kernel. -/
theorem IdealSheafData.ofSpfOnSpace_ideal (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (I : Ideal (A : Type u)) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (U : (FormalScheme.ofSpfOnSpace A hA e).affineOpens) :
    (IdealSheafData.ofSpfOnSpace A hA e I hI).ideal U =
      RingHom.ker (IdealSheafData.spfQuotientProjection A e I hI U.1) :=
  rfl

/-- An ideal sheaf is a weak ideal of definition when its sections on every
formal affine open are a weak ideal of definition. -/
def IsWeakIdealOfDefinition {X : FormalScheme.{u}} (I : IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U)

/-- Unfolding of `IsWeakIdealOfDefinition`. -/
theorem isWeakIdealOfDefinition_iff {X : FormalScheme.{u}} (I : IdealSheafData X) :
    IsWeakIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U) :=
  Iff.rfl

/-- Quotient-projection kernels of weak ideals are weak ideals on the formal spectrum. -/
theorem isWeakIdealOfDefinition_ofSpfOnSpace (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (I : Ideal (A : Type u)) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    IsWeakIdealOfDefinition (IdealSheafData.ofSpfOnSpace A hA e I hI) :=
  sorry

/-- Being a weak ideal of definition may be checked on the members of an affine
open covering. -/
theorem isWeakIdealOfDefinition_iff_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsWeakIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
