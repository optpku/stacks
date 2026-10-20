module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Dual numbers as an object of `ArtinianLocalAlgCat`

The dual numbers `DualNumber k` bundle as the object `k[ε]` of `C_Λ`, together with the
canonical projection onto the residue field `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.dualNumberResidueFieldIso Λ k :
  ResidueField (DualNumber k) ≃ₐ[Λ] k)

#check (ArtinianLocalAlgCat.dualNumber Λ k : ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.dualNumberToResidue Λ k :
  ArtinianLocalAlgCat.dualNumber Λ k ⟶ ArtinianLocalAlgCat.residue Λ k)
