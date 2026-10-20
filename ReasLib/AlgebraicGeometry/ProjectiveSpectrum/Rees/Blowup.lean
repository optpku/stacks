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
      Ideal.comap (algebraMap A (reesAlgebra I)) x.asHomogeneousIdeal.toIdeal := sorry

/-- The open complement of the center in the base affine scheme. -/
def openAway (I : Ideal A) : (Spec (.of A)).Opens where
  carrier := (PrimeSpectrum.zeroLocus (I : Set A))ᶜ
  is_open' := (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl

/-- The carrier of the open complement is the complement of the center's zero locus. -/
theorem coe_openAway (I : Ideal A) :
    (openAway I : Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := sorry

/-- A base point lies in the open complement exactly when its prime avoids the center. -/
theorem mem_openAway_iff (I : Ideal A) (ξ : Spec (.of A)) :
    ξ ∈ openAway I ↔ ¬ I ≤ ξ.asIdeal := sorry

/-- For a generic point, avoiding the center is equivalent to the closed set not lying in it. -/
theorem genericPoint_mem_openAway_iff_not_subset (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ ¬ Z ⊆ PrimeSpectrum.zeroLocus (I : Set A) := sorry

/-- For a generic point, avoiding the center is equivalent to meeting the open complement. -/
theorem genericPoint_mem_openAway_iff_nonempty (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ (Z ∩ openAway I).Nonempty := sorry

/-- For a generic point, avoiding the center is equivalent to not belonging to its zero locus. -/
theorem genericPoint_mem_openAway_iff_not_mem_zeroLocus (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)} (hξ : IsGenericPoint ξ Z) :
    ξ ∈ openAway I ↔ ξ ∉ PrimeSpectrum.zeroLocus (I : Set A) := sorry

/-- The Rees blowup morphism restricts to a homeomorphism away from the center. -/
theorem isHomeomorph_restrict_openAway (I : Ideal A) :
    IsHomeomorph (toSpec I ∣_ openAway I).base := sorry

/-- Every point outside the center has a unique preimage under the Rees blowup morphism. -/
theorem existsUnique_preimage (I : Ideal A) {ξ : Spec (.of A)} (hξ : ξ ∈ openAway I) :
    ∃! x : Proj (ReesAlgebra.Grading.grade I), toSpec I x = ξ := sorry

/-- An irreducible closed set meeting the open complement has strict transform equal to the
closure of the point above its generic point. -/
theorem strictTransform_eq_closure_singleton (I : Ideal A)
    {Z : Set (Spec (.of A))} {ξ : Spec (.of A)}
    {ξ' : Proj (ReesAlgebra.Grading.grade I)} (hξ : IsGenericPoint ξ Z)
    (hU : ξ ∈ openAway I) (hξ' : toSpec I ξ' = ξ) :
    ReesAlgebra.strictTransform I Z = closure {ξ'} := sorry

end AlgebraicGeometry.ReesProj
