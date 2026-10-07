module

public import Mathlib.Algebra.Algebra.Tower
public import stacks_project.Chap90.Definition_90_10_1_DualNumber

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

/-- The canonical inclusion `residue Λ k ⟶ dualNumber Λ k` in `ArtinianLocalAlgCat`,
given on underlying algebras by `a ↦ a`. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k where
  hom := (inlAlgHom k k k).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueToDualNumber` is the dual-number inclusion. -/
theorem residueToDualNumber_hom :
    (residueToDualNumber Λ k).hom = (inlAlgHom k k k).restrictScalars Λ := sorry

/-- The inclusion `k ⟶ k[ε]` followed by the coefficient projection is the identity on `k`. -/
theorem residueToDualNumber_comp_dualNumberToResidue :
    residueToDualNumber Λ k ≫ dualNumberToResidue Λ k = 𝟙 (residue Λ k) := sorry

/-- The morphism `residueToDualNumber` is a local homomorphism. -/
theorem residueToDualNumber_isLocalHom :
    IsLocalHom (residueToDualNumber Λ k).hom := sorry

/-- The morphism `residueToDualNumber` is compatible with residue identifications. -/
theorem residueToDualNumber_residue_compat :
    (dualNumber Λ k).residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (residueToDualNumber Λ k).hom) =
      (residue Λ k).residueFieldIso.toAlgHom := sorry

end ArtinianLocalAlgCat
