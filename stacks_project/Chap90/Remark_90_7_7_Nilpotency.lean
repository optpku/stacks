/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Nilpotency
public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration.Artinian

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.7: compatibility checks for the nilpotency-stage quotient identification. -/
#check (ArtinianLocalAlgCat.nilpotencyIndex : ArtinianLocalAlgCat Λ k → ℕ)

#check (ArtinianLocalAlgCat.nilpotencyIndex_pow_eq_bot : ∀ (A : ArtinianLocalAlgCat Λ k),
  CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (nilpotencyIndex A + 1) = ⊥)

#check (ArtinianLocalAlgCat.toTruncation : ∀ (A : ArtinianLocalAlgCat Λ k) (n : ℕ),
  A ⟶ (toComplete A).truncation n)

#check (ArtinianLocalAlgCat.truncationNilpotencyIso : ∀ (A : ArtinianLocalAlgCat Λ k),
  (toComplete A).truncation (nilpotencyIndex A) ≅ A)

#check (CompleteLocalAlgCat.AdicIdealFiltration.zero : ∀ (R : CompleteLocalAlgCat Λ k)
  [IsArtinianRing R.carrier], CompleteLocalAlgCat.AdicIdealFiltration R)
