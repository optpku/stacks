/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReasLib.RingTheory.Excellent.CompleteLocal
public import ReasLib.RingTheory.Excellent.Dedekind
public import ReasLib.RingTheory.Excellent.EssentialFiniteness
public import ReasLib.RingTheory.Excellent.Field
public import ReasLib.RingTheory.Excellent.Nagata

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

private theorem hasRingPropertyLocally_of_locallyOfFiniteType
    {X S : Scheme.{u}} (P : CommRingCat.{u} → Prop) (f : X ⟶ S)
    [hS : S.HasRingPropertyLocally P] [LocallyOfFiniteType f]
    (hP : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
      φ.hom.FiniteType → P A → P B) : X.HasRingPropertyLocally P := by
  refine ⟨?_⟩
  intro x
  obtain ⟨V, hxV, hV⟩ := hS.out (f x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ (V : S.Opens) from hxV)
      (f ⁻¹ᵁ (V : S.Opens)).isOpen
  have hUV' : U ≤ f ⁻¹ᵁ (V : S.Opens) := hUV
  exact ⟨⟨U, hU⟩, hxU, hP (f.appLE (V : S.Opens) U hUV')
    (f.finiteType_appLE V.2 hU hUV') hV⟩

private theorem excellent_spec_of_isExcellentRing (R : Type u) [CommRing R]
    [IsExcellentRing.{u, u} R] : Excellent (Spec (CommRingCat.of R)) := by
  refine ⟨?_⟩
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  have hft := RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  algebraize [(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom]
  exact IsExcellentRing.of_finiteType R

/-- Quasi-excellence implies the Nagata property. -/
theorem nagata_of_quasiExcellent (X : Scheme.{u}) [QuasiExcellent X] :
    Nagata X := by
  refine ⟨?_⟩
  intro x
  obtain ⟨U, hxU, hU⟩ := (inferInstance : QuasiExcellent X).out x
  letI : IsQuasiExcellentRing.{u, u} (Γ(X, U)) := hU
  exact ⟨U, hxU, IsQuasiExcellentRing.nagataRing (Γ(X, U))⟩

/-- Local finite type preserves quasi-excellence. -/
theorem quasiExcellent_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiExcellent S] [LocallyOfFiniteType f] : QuasiExcellent X := by
  apply hasRingPropertyLocally_of_locallyOfFiniteType
    (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u, u} A) f
  intro A B φ hft hA
  letI : IsQuasiExcellentRing.{u, u} A := hA
  algebraize [φ.hom]
  exact IsQuasiExcellentRing.of_finiteType A

/-- Local finite type preserves excellence. -/
theorem excellent_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [Excellent S] [LocallyOfFiniteType f] : Excellent X := by
  apply hasRingPropertyLocally_of_locallyOfFiniteType
    (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u, u} A) f
  intro A B φ hft hA
  letI : IsExcellentRing.{u, u} A := hA
  algebraize [φ.hom]
  exact IsExcellentRing.of_finiteType A

/-- Schemes locally of finite type over a field are excellent. -/
theorem excellent_of_locallyOfFiniteType_field {X : Scheme.{u}}
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] : Excellent X := by
  letI : IsExcellentRing.{u, u} k := inferInstance
  letI : Excellent (Spec (CommRingCat.of k)) := excellent_spec_of_isExcellentRing k
  exact excellent_of_locallyOfFiniteType f

/-- Schemes locally of finite type over a Noetherian complete local ring are excellent. -/
theorem excellent_of_locallyOfFiniteType_completeLocal {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] : Excellent X := by
  letI : IsCompleteLocalRing R := inferInstance
  letI : IsExcellentRing.{u, u} R := inferInstance
  letI : Excellent (Spec (CommRingCat.of R)) := excellent_spec_of_isExcellentRing R
  exact excellent_of_locallyOfFiniteType f

/-- Schemes locally of finite type over the integers are excellent. -/
theorem excellent_of_locallyOfFiniteType_int {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) [LocallyOfFiniteType f] :
    Excellent X := by
  letI : IsExcellentRing.{0, u} ℤ := inferInstance
  letI : IsExcellentRing.{u, u} (ULift.{u} ℤ) :=
    IsExcellentRing.of_finiteType ℤ
  letI : Excellent (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    excellent_spec_of_isExcellentRing (ULift.{u} ℤ)
  exact excellent_of_locallyOfFiniteType f

/-- Schemes locally of finite type over a characteristic-zero Dedekind domain are excellent. -/
theorem excellent_of_locallyOfFiniteType_dedekindCharZero {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] : Excellent X := by
  letI : IsExcellentRing.{u, u} R := inferInstance
  letI : Excellent (Spec (CommRingCat.of R)) := excellent_spec_of_isExcellentRing R
  exact excellent_of_locallyOfFiniteType f

end AlgebraicGeometry.Scheme
