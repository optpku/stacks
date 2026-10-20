/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeaklyAdmissible
public import stacks_project.Chap87.«87_2_0_1_Spf»

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace

namespace AlgebraicGeometry.McQuillan

/-- The record and subtype presentations of open prime ideals are homeomorphic. -/
def legacyOpenPrimeHomeomorph {A : Type u} [CommRing A] [TopologicalSpace A] :
    AlgebraicGeometry.OpenPrime A ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime A where
  toFun p := ⟨p.toPrimeSpectrum, p.isOpen⟩
  invFun p := ⟨p.val, p.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

/-- The quotient-spectrum open associated to an open in the record presentation. -/
def pullbackOpens {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (U : Opens (AlgebraicGeometry.OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : Opens (PrimeSpectrum (A ⧸ I)) :=
  FormalSpectrum.pullbackOpens legacyOpenPrimeHomeomorph U I hI

#check (AlgebraicGeometry.McQuillan.FormalSpectrum.OpenPrime.homeomorphQuotient :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A), TopologicalRing.Ideal.IsWeakIdealOfDefinition I →
    AlgebraicGeometry.FormalSpectrum.OpenPrime A ≃ₜ PrimeSpectrum (A ⧸ I))

#check (AlgebraicGeometry.McQuillan.FormalSpectrum.Sections.ofCompatible :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime A)
    (U : Opens T) (s : FormalSpectrum.ComponentFamily e U),
    FormalSpectrum.IsCompatible e U s → FormalSpectrum.Sections e U)

#check (AlgebraicGeometry.McQuillan.spf :
  ∀ (A : TopCommRingCat.{u}), TopologicalRing.IsWeaklyAdmissibleRing A →
    LocallyTopologicallyRingedSpaceCat.{u})

end AlgebraicGeometry.McQuillan
