/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

@[expose] public section

open IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {Λ k}

/- Definition 90.3.1 classical API compatibility checks. -/
#check (IsClassical Λ k : Prop)
#check (instIsClassicalResidueField :
  ∀ [IsCompleteLocalRing Λ], IsClassical Λ (ResidueField Λ))
#check (isClassical_iff :
  IsClassical Λ k ↔ IsCompleteLocalRing Λ ∧ Function.Surjective (algebraMap Λ k))
#check (IsClassical.residueFieldIso : [IsClassical Λ k] → ResidueField Λ ≃ₐ[Λ] k)
#check (IsClassical.residueFieldIso_residue :
  [IsClassical Λ k] → (x : Λ) →
    IsClassical.residueFieldIso (residue Λ x) = algebraMap Λ k x)
#check (ofResidueFieldIso :
  [IsCompleteLocalRing Λ] → (ResidueField Λ ≃ₐ[Λ] k) → IsClassical Λ k)

end ArtinianLocalAlgCat
