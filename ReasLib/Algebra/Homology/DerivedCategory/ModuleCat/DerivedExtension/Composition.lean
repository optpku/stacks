/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of explicit derived extension models

Explicit derived extension models compose because their right adjoints compose as derived
restriction of scalars.  The resulting model remains concrete data; uniqueness of left adjoints
then supplies comparisons with every other model along the same ring map.
@stack 064M
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Compose explicit derived extension models along two composable ring homomorphisms. -/
@[stacks 064M "composition of explicit derived extension models"]
noncomputable def comp {σ : R →+* S} {τ : S →+* T}
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ) :
    DerivedExtension (τ.comp σ) where
  toFunctor := Eσ.toFunctor ⋙ Eτ.toFunctor
  adjunction := (Eσ.adjunction.comp Eτ.adjunction).ofNatIsoRight
    (DerivedRestriction.compIso σ τ).symm

/-- Compose explicit derived extension models when the target ring homomorphism is named
separately from its composite presentation. -/
@[stacks 064M "composition of explicit derived extension models along an identified map"]
noncomputable def compOfEq {σ : R →+* S} {τ : S →+* T} (ρ : R →+* T)
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ) (hρ : ρ = τ.comp σ) :
    DerivedExtension ρ where
  toFunctor := Eσ.toFunctor ⋙ Eτ.toFunctor
  adjunction := (Eσ.adjunction.comp Eτ.adjunction).ofNatIsoRight
    (DerivedRestriction.compIsoOfEq σ τ ρ hρ).symm

/-- The iterated explicit extension model is canonically isomorphic to any direct model along
the strict composite. -/
@[stacks 064M "comparison of iterated and direct explicit derived extension"]
noncomputable def compIso {σ : R →+* S} {τ : S →+* T}
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ)
    (Eστ : DerivedExtension (τ.comp σ)) :
    Eσ.toFunctor ⋙ Eτ.toFunctor ≅ Eστ.toFunctor :=
  (Eσ.comp Eτ).iso Eστ

/-- Objectwise comparison between iterated and direct explicit derived extension along a strict
composite. -/
noncomputable abbrev compObjIso {σ : R →+* S} {τ : S →+* T}
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ)
    (Eστ : DerivedExtension (τ.comp σ))
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    Eτ.obj (Eσ.obj K) ≅ Eστ.obj K :=
  (compIso Eσ Eτ Eστ).app K

/-- The iterated explicit extension model is canonically isomorphic to any direct model along a
ring homomorphism identified with the composite. -/
@[stacks 064M "comparison along an identified composite ring homomorphism"]
noncomputable def compIsoOfEq {σ : R →+* S} {τ : S →+* T} (ρ : R →+* T)
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ) (Eρ : DerivedExtension ρ)
    (hρ : ρ = τ.comp σ) :
    Eσ.toFunctor ⋙ Eτ.toFunctor ≅ Eρ.toFunctor :=
  (compOfEq ρ Eσ Eτ hρ).iso Eρ

/-- Objectwise comparison between iterated extension and a direct model along a named composite
ring homomorphism. -/
noncomputable abbrev compObjIsoOfEq {σ : R →+* S} {τ : S →+* T} (ρ : R →+* T)
    (Eσ : DerivedExtension σ) (Eτ : DerivedExtension τ) (Eρ : DerivedExtension ρ)
    (hρ : ρ = τ.comp σ) (K : DerivedCategory (ModuleCat.{u, u} R)) :
    Eτ.obj (Eσ.obj K) ≅ Eρ.obj K :=
  (compIsoOfEq ρ Eσ Eτ Eρ hρ).app K

end CategoryTheory.ModuleCat.DerivedExtension
