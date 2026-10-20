/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section

/-!
# The dual-number extension morphism in `ArtinianLocalAlgCat`

The source map `k ⟶ k[ε]`, `a ↦ a`, as a morphism of residue-identified Artinian local
`Λ`-algebras, together with its composite with the canonical projection `k[ε] ⟶ k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

#check (ArtinianLocalAlgCat.residueToDualNumber Λ k : residue Λ k ⟶ dualNumber Λ k)

#check (ArtinianLocalAlgCat.residueToDualNumber_hom Λ k :
  (residueToDualNumber Λ k).hom = (inlAlgHom k k k).restrictScalars Λ)

#check (ArtinianLocalAlgCat.residueToDualNumber_comp_dualNumberToResidue Λ k :
  residueToDualNumber Λ k ≫ dualNumberToResidue Λ k = 𝟙 (residue Λ k))

#check (ArtinianLocalAlgCat.residueToDualNumber_isLocalHom Λ k :
  IsLocalHom (residueToDualNumber Λ k).hom)

#check (ArtinianLocalAlgCat.residueToDualNumber_residue_compat Λ k :
  residueCompat (residueToDualNumber Λ k).hom (residueToDualNumber Λ k).isLocalHom =
    residueIsoHom (residue Λ k))

end ArtinianLocalAlgCat
