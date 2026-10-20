/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-! Compatibility checks for the complete local algebra category. -/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.of_carrier :
  ∀ (X : Type u) [CommRing X] [Algebra Λ X] [IsNoetherianRing X]
    [IsCompleteLocalRing X] (residueFieldIso : ResidueField X ≃ₐ[Λ] k),
    (CompleteLocalAlgCat.of X residueFieldIso).carrier = X)

#check (CompleteLocalAlgCat.truncationMap_hom :
  ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ),
    (R.truncationMap n).hom =
      CompleteLocalAlgCat.truncationFactor R n)
