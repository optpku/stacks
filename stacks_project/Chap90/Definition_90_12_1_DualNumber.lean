/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Dual numbers as an object of `ArtinianLocalAlgCat`

The dual numbers `DualNumber k` bundle as the object `k[ε]` of `C_Λ`, together with the
canonical identification of the residue field with `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.dualNumberResidueFieldIso Λ k :
  ResidueField (DualNumber k) ≃ₐ[Λ] k)

#check (ArtinianLocalAlgCat.dualNumberResidueFieldIso_apply Λ k :
  ∀ x : DualNumber k,
    ArtinianLocalAlgCat.dualNumberResidueFieldIso Λ k (residue (DualNumber k) x) = x.fst)

#check (ArtinianLocalAlgCat.dualNumber Λ k : ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.dualNumber_carrier Λ k :
  (ArtinianLocalAlgCat.dualNumber Λ k).carrier = DualNumber k)

/- The dual-number object is Artinian local with its canonical residue identification. -/
example :
    IsLocalRing (ArtinianLocalAlgCat.dualNumber Λ k).carrier ∧
      IsArtinianRing (ArtinianLocalAlgCat.dualNumber Λ k).carrier ∧
      (ArtinianLocalAlgCat.dualNumber Λ k).residueFieldIso =
        ArtinianLocalAlgCat.dualNumberResidueFieldIso Λ k :=
  ⟨inferInstance, inferInstance, rfl⟩
