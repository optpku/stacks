/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Inclusion
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances

/-!
# Quotient projections to complete-local truncations
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The quotient map to a positive maximal-adic truncation is local. -/
theorem truncationToInclusion_isLocalHom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (n + 1))) := sorry

/-- The quotient map to a maximal-adic truncation preserves the residue identification. -/
theorem truncationToInclusion_residue_compat (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    residueCompat (A := R) (B := ArtinianLocalAlgCat.inclusion.obj (R.truncation n))
      (Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (n + 1)))
      (truncationToInclusion_isLocalHom R n) = residueIsoHom R := sorry

/-- The canonical projection from a complete local algebra to its included maximal-adic
truncation. -/
def truncationToInclusion (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (R.truncation n) :=
  Hom.of (Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (n + 1)))
    (truncationToInclusion_isLocalHom R n) (truncationToInclusion_residue_compat R n)

/-- The underlying algebra map of the truncation projection is the quotient map. -/
theorem truncationToInclusion_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationToInclusion R n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (n + 1)) := rfl

end CompleteLocalAlgCat
