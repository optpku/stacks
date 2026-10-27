/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.StrictTransform
public import ReasLib.RingTheory.ReesAlgebra.Grading.Zero

/-!
# Scheme-theoretic geometry of a Rees blowup

This module records the morphism from the projective spectrum of a Rees algebra
to the affine spectrum of its coefficient ring, together with its restriction
away from the center and the generic-point description of strict transforms.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Polynomial
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ReesProj

variable {A : Type u} [CommRing A]

/-- The canonical identification of the degree-zero Rees spectrum with the base spectrum. -/
def degreeZeroSpecIso (I : Ideal A) :
    Spec (.of (ReesAlgebra.Grading.grade I 0)) ≅ Spec (.of A) :=
  (Scheme.Spec.mapIso (ReesAlgebra.Grading.degreeZeroRingEquiv I).toCommRingCatIso.op).symm

/-- The canonical morphism from the Rees projective spectrum to the base spectrum. -/
def toSpec (I : Ideal A) :
    Proj (ReesAlgebra.Grading.grade I) ⟶ Spec (.of A) :=
  Proj.toSpecZero (ReesAlgebra.Grading.grade I) ≫ (degreeZeroSpecIso I).hom

/-- The base ideal of a point under the Rees blowup morphism is the contracted homogeneous ideal. -/
theorem toSpec_base_asIdeal (I : Ideal A)
    (x : Proj (ReesAlgebra.Grading.grade I)) :
    ((toSpec I).base x).asIdeal =
      Ideal.comap (algebraMap A (reesAlgebra I)) x.asHomogeneousIdeal.toIdeal := by
  let 𝒜 := ReesAlgebra.Grading.grade I
  let y : (Proj.basicOpen 𝒜 1).toScheme :=
    ((Scheme.topIso (Proj 𝒜)).inv ≫ (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv) x
  have hy : y.1 = x := by
    dsimp only [y]
    simp only [Scheme.Hom.comp_apply, Scheme.isoOfEq_inv, Scheme.homOfLE_apply]
    exact congrArg (fun f : Proj 𝒜 ⟶ Proj 𝒜 => f x) (Scheme.topIso (Proj 𝒜)).inv_hom_id
  ext a
  change ReesAlgebra.Grading.zeroAlgebraMap I a ∈
    ((Proj.toSpecZero 𝒜).base x).asIdeal ↔ _
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (1 : reesAlgebra I))
    (ReesAlgebra.Grading.zeroAlgebraMap I a) ∈
      ((ProjectiveSpectrum.Proj.toSpec 𝒜 1).base y).asIdeal ↔ _
  refine (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 y
    ⟨0, ReesAlgebra.Grading.zeroAlgebraMap I a, 1, one_mem _⟩).trans ?_
  change algebraMap A (reesAlgebra I) a ∈ y.1.asHomogeneousIdeal ↔ _
  rw [hy]
  exact Iff.rfl

/-- The open complement of the center in the base affine scheme. -/
def openAway (I : Ideal A) : (Spec (.of A)).Opens where
  carrier := (PrimeSpectrum.zeroLocus (I : Set A))ᶜ
  is_open' := (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl

/-- The carrier of the open complement is the complement of the center's zero locus. -/
theorem coe_openAway (I : Ideal A) :
    (openAway I : Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := rfl

/-- A base point lies in the open complement exactly when its prime avoids the center. -/
theorem mem_openAway_iff (I : Ideal A) (ξ : Spec (.of A)) :
    ξ ∈ openAway I ↔ ¬ I ≤ ξ.asIdeal := by
  exact not_congr (PrimeSpectrum.mem_zeroLocus ξ (I : Set A))

/-- For a generic point, avoiding the center is equivalent to the closed set not lying in it. -/
theorem genericPoint_mem_openAway_iff_not_subset (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ ¬ Z ⊆ PrimeSpectrum.zeroLocus (I : Set A) := by
  exact not_congr (hξ.mem_closed_set_iff (PrimeSpectrum.isClosed_zeroLocus (I : Set A)))

/-- For a generic point, avoiding the center is equivalent to meeting the open complement. -/
theorem genericPoint_mem_openAway_iff_nonempty (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ (Z ∩ openAway I).Nonempty := by
  exact hξ.mem_open_set_iff (openAway I).isOpen

/-- For a generic point, avoiding the center is equivalent to not belonging to its zero locus. -/
theorem genericPoint_mem_openAway_iff_not_mem_zeroLocus (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ ξ ∉ PrimeSpectrum.zeroLocus (I : Set A) := Iff.rfl

/-- The Rees blowup morphism restricts to a homeomorphism away from the center. -/
theorem isHomeomorph_restrict_openAway (I : Ideal A) :
    IsHomeomorph (toSpec I ∣_ openAway I).base := sorry

/-- Every point outside the center has a unique preimage under the Rees blowup morphism. -/
theorem existsUnique_preimage (I : Ideal A) {ξ : Spec (.of A)} (hξ : ξ ∈ openAway I) :
    ∃! x : Proj (ReesAlgebra.Grading.grade I), toSpec I x = ξ := by
  obtain ⟨x, hx⟩ := (isHomeomorph_restrict_openAway I).surjective ⟨ξ, hξ⟩
  have hx' : toSpec I x.1 = ξ := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx
  refine ⟨x.1, hx', ?_⟩
  intro y hy
  have hyU : y ∈ (toSpec I ⁻¹ᵁ openAway I) := by
    change toSpec I y ∈ openAway I
    rw [hy]
    exact hξ
  have hyx : (toSpec I ∣_ openAway I) ⟨y, hyU⟩ =
      (toSpec I ∣_ openAway I) x := by
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hy.trans hx'.symm
  exact congrArg Subtype.val ((isHomeomorph_restrict_openAway I).injective hyx)

/-- An irreducible closed set meeting the open complement has strict transform equal to the
closure of the point above its generic point. -/
theorem strictTransform_eq_closure_singleton (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)}
    {ξ' : Proj (ReesAlgebra.Grading.grade I)} (hξ : IsGenericPoint ξ Z)
    (hU : ξ ∈ openAway I) (hξ' : toSpec I ξ' = ξ) :
    ReesAlgebra.strictTransform I Z = closure {ξ'} := by
  have hmap : ReesAlgebra.toSpec I = (toSpec I).base := by
    funext x
    apply PrimeSpectrum.ext
    exact (toSpec_base_asIdeal I x).symm
  rw [ReesAlgebra.strictTransform_def, hmap]
  have hxU : ξ' ∈ (toSpec I ⁻¹ᵁ openAway I) := by
    change toSpec I ξ' ∈ openAway I
    rw [hξ']
    exact hU
  let ξU : (toSpec I ⁻¹ᵁ openAway I).toScheme := ⟨ξ', hxU⟩
  have hhome := isHomeomorph_restrict_openAway I
  have hind := (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hhome.continuous hhome.injective hhome.isOpenMap).isInducing
  apply subset_antisymm
  · apply closure_minimal ?_ isClosed_closure
    intro y hy
    let yU : (toSpec I ⁻¹ᵁ openAway I).toScheme := ⟨y, hy.2⟩
    have hs : (toSpec I ∣_ openAway I) ξU ⤳ (toSpec I ∣_ openAway I) yU := by
      apply (subtype_specializes_iff _ _).mpr
      simpa only [morphismRestrict_base_coe, ξU, yU, hξ'] using hξ.specializes hy.1
    exact specializes_iff_mem_closure.mp
      ((subtype_specializes_iff ξU yU).mp (hind.specializes_iff.mp hs))
  · apply closure_mono
    intro y hy
    obtain rfl : y = ξ' := hy
    exact ⟨hξ' ▸ hξ.mem, hξ' ▸ hU⟩

end AlgebraicGeometry.ReesProj
