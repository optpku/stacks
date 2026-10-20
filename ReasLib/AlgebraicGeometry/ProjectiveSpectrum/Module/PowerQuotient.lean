/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
public import ReasLib.RingTheory.MvPolynomial.PowerQuotient

/-!
# Coordinate-power quotients on projective spectra

This file records the associated sheaf and degree-zero section map of coordinate-power
quotients, together with the finite-variable vanishing and non-bijectivity properties.
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj.PowerQuotient

variable {σ : Type u} {k : Type v} [CommRing k]

/-- A pigeonhole power of the irrelevant ideal annihilates the quotient by fixed positive
powers of all coordinate variables. -/
theorem irrelevant_pow_le_annihilator [Fintype σ] (e : ℕ+) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.standardGrading σ k)).toIdeal ^
        (Fintype.card σ * ((e : ℕ) - 1) + 1) ≤
      Module.annihilator (MvPolynomial σ k)
        (MvPolynomial.PowerQuotient.Quotient (σ := σ) (k := k) e) := sorry

/-- The sheaf on projective space associated to the integer-graded coordinate-power quotient. -/
noncomputable def associatedSheaf (e : ℕ+) :
    (AlgebraicGeometry.Proj (MvPolynomial.standardGrading σ k)).Modules :=
  AlgebraicGeometry.Proj.AssociatedModule.sheaf
    (MvPolynomial.standardGrading σ k)
    (MvPolynomial.PowerQuotient.integerGrading (σ := σ) (k := k) e)

/-- The canonical linear map from the degree-zero coordinate-power quotient to the global
sections of its associated sheaf. -/
noncomputable def degreeZeroSectionMap (e : ℕ+) :=
  AlgebraicGeometry.Proj.AssociatedModule.degreeZeroToGlobalSections
    (MvPolynomial.standardGrading σ k)
    (MvPolynomial.PowerQuotient.integerGrading (σ := σ) (k := k) e)

/-- The sheaf associated to a finite-variable coordinate-power quotient is zero. -/
theorem associatedSheaf_isZero [Fintype σ] (e : ℕ+) :
    CategoryTheory.Limits.IsZero (associatedSheaf (σ := σ) (k := k) e) := sorry

/-- The canonical degree-zero map to global sections of the associated sheaf is not
bijective. -/
theorem degreeZeroSectionMap_not_bijective [Fintype σ] [Nontrivial k] (e : ℕ+) :
    ¬ Function.Bijective (degreeZeroSectionMap (σ := σ) (k := k) e) := sorry

end AlgebraicGeometry.Proj.PowerQuotient
