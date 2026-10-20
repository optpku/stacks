/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.StrictTransform

/-!
# Topological strict transform on Proj of a Rees algebra

This compatibility bridge checks the contraction and topological strict-transform
API and retains the aggregate import of the Rees grading.
-/

@[expose] public section

noncomputable section

universe u

open ReesAlgebra

#check (ReesAlgebra.toSpec :
  {A : Type u} → [CommRing A] → (I : Ideal A) →
    ProjectiveSpectrum (Grading.grade I) → PrimeSpectrum A)

#check (ReesAlgebra.toSpec_asIdeal :
  ∀ {A : Type u} [CommRing A] (I : Ideal A)
    (point : ProjectiveSpectrum (Grading.grade I)),
    (toSpec I point).asIdeal =
      Ideal.comap (algebraMap A (reesAlgebra I)) point.asHomogeneousIdeal.toIdeal)

#check (ReesAlgebra.toSpec_continuous :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), Continuous (toSpec I))

#check (ReesAlgebra.openAway :
  {A : Type u} → [CommRing A] → Ideal A → Set (PrimeSpectrum A))

#check (ReesAlgebra.openAway_def :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    openAway I = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ)

#check (ReesAlgebra.strictTransform :
  {A : Type u} → [CommRing A] → (I : Ideal A) → Set (PrimeSpectrum A) →
    Set (ProjectiveSpectrum (Grading.grade I)))

#check (ReesAlgebra.strictTransform_def :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (Z : Set (PrimeSpectrum A)),
    strictTransform I Z = closure (toSpec I ⁻¹' (Z ∩ openAway I)))

#check (ReesAlgebra.isClosed_strictTransform :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (Z : Set (PrimeSpectrum A)),
    IsClosed (strictTransform I Z))
