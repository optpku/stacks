/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.InverseLimit
public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration

/-!
# Inverse limits of surjective towers in `C_Λ`

A surjective sequence in `ArtinianLocalAlgCat` with bounded cotangent rank has
inverse limit an object of `CompleteLocalAlgCat`, and the kernels of the
projections define the maximal-adic topology.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

variable (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)

/-- A surjective Artinian-local tower with bounded cotangent dimensions has a Noetherian limit. -/
theorem inverseLimit_isNoetherianRing
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    IsNoetherianRing (ArtinianLocalAlgCat.inverseLimit A f) := sorry

/-- A surjective Artinian-local tower with bounded cotangent dimensions has a complete local limit. -/
theorem inverseLimit_isCompleteLocalRing
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    IsCompleteLocalRing (ArtinianLocalAlgCat.inverseLimit A f) := sorry

/-- The inverse limit of a surjective Artinian-local tower with bounded cotangent dimensions,
viewed as a complete local algebra with its canonical residue identification. -/
noncomputable def ofInverseLimit
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    CompleteLocalAlgCat Λ k :=
  ⟨CommRingCat.of (ArtinianLocalAlgCat.inverseLimit A f),
    ArtinianLocalAlgCat.instAlgebra_inverseLimit A f,
    ArtinianLocalAlgCat.instIsLocalRing_inverseLimit A f,
    inverseLimit_isNoetherianRing A f hf hdim,
    inverseLimit_isCompleteLocalRing A f hf hdim,
    ArtinianLocalAlgCat.inverseLimitResidueFieldIso A f hf⟩

/-- The carrier of `ofInverseLimit` is the inverse-limit ring of the tower. -/
theorem ofInverseLimit_carrier
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    (ofInverseLimit A f hf hdim).carrier = ArtinianLocalAlgCat.inverseLimit A f := sorry

/-- `ofInverseLimit` is Noetherian and complete, with the canonical residue identification. -/
theorem ofInverseLimit_spec
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    IsNoetherianRing (ofInverseLimit A f hf hdim).carrier ∧
      IsCompleteLocalRing (ofInverseLimit A f hf hdim).carrier ∧
        (ofInverseLimit A f hf hdim).residueFieldIso =
          ArtinianLocalAlgCat.inverseLimitResidueFieldIso A f hf := sorry

/-- Projection kernels of an inverse limit form a decreasing family of ideals. -/
theorem inverseLimit_ker_antitone : Antitone (ArtinianLocalAlgCat.ker A f) := sorry

/-- Every projection kernel is contained in the maximal ideal of the inverse limit. -/
theorem inverseLimit_ker_le_maximal (n : ℕ) :
    ArtinianLocalAlgCat.ker A f n ≤ IsLocalRing.maximalIdeal (ArtinianLocalAlgCat.inverseLimit A f) := sorry

/-- Projection kernels are eventually contained in each positive maximal-adic power
for a surjective Artinian-local tower with bounded cotangent dimensions. -/
theorem inverseLimit_ker_exists_le_pow
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B)
    (n : ℕ) :
    ∃ m, ArtinianLocalAlgCat.ker A f m ≤
      IsLocalRing.maximalIdeal (ArtinianLocalAlgCat.inverseLimit A f) ^ (n + 1) := sorry

/-- Every projection kernel contains a positive maximal-adic power. -/
theorem inverseLimit_ker_exists_pow_le (n : ℕ) :
    ∃ m, IsLocalRing.maximalIdeal (ArtinianLocalAlgCat.inverseLimit A f) ^ (m + 1) ≤
      ArtinianLocalAlgCat.ker A f n := sorry

/-- Projection kernels give a maximal-adic filtration of the inverse limit of a surjective
Artinian-local tower with bounded cotangent dimensions. -/
noncomputable def kerAdicFiltration
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    AdicIdealFiltration (ofInverseLimit A f hf hdim) :=
  AdicIdealFiltration.of (ArtinianLocalAlgCat.ker A f)
    (inverseLimit_ker_antitone A f) (inverseLimit_ker_le_maximal A f)
    (inverseLimit_ker_exists_le_pow A f hf hdim) (inverseLimit_ker_exists_pow_le A f)

/-- The underlying ideals of `kerAdicFiltration` are the kernels of the projections. -/
theorem kerAdicFiltration_ideal
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B)
    (n : ℕ) :
    (kerAdicFiltration A f hf hdim).ideal n = ArtinianLocalAlgCat.ker A f n := sorry

/-- `kerAdicFiltration` is antitone, contained in the maximal ideal, and cofinal with
the maximal-adic powers in both directions. -/
theorem kerAdicFiltration_spec
    (hf : ∀ n, Function.Surjective (f n).hom)
    (hdim : ∃ B : ℕ, ∀ n,
      Module.finrank (ResidueField (A n).carrier) (CotangentSpace (A n).carrier) ≤ B) :
    Antitone (kerAdicFiltration A f hf hdim).ideal ∧
      (∀ n, (kerAdicFiltration A f hf hdim).ideal n ≤
        IsLocalRing.maximalIdeal (ofInverseLimit A f hf hdim).carrier) ∧
      (∀ n, ∃ m, (kerAdicFiltration A f hf hdim).ideal m ≤
        IsLocalRing.maximalIdeal (ofInverseLimit A f hf hdim).carrier ^ (n + 1)) ∧
      (∀ n, ∃ m, IsLocalRing.maximalIdeal (ofInverseLimit A f hf hdim).carrier ^ (m + 1) ≤
        (kerAdicFiltration A f hf hdim).ideal n) := sorry

end CompleteLocalAlgCat
