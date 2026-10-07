module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Logic.Unique
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable

/-!
# Canonical residue morphism in `CompleteLocalAlgCat`

Every object `R` of `CompleteLocalAlgCat Λ k` admits a unique morphism to the
residue field `k`, obtained by composing the quotient map to
`ResidueField R.carrier` with the residue identification of `R`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The canonical morphism `R ⟶ inclusion.obj (residue Λ k)` induced by the residue
identification of `R`. -/
noncomputable def residueHom (R : CompleteLocalAlgCat Λ k) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k) where
  hom := R.residueFieldIso.toAlgHom.comp
    (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueHom` is the residue identification after
the quotient map to the residue field. -/
theorem residueHom_hom (R : CompleteLocalAlgCat Λ k) :
    (residueHom R).hom =
      R.residueFieldIso.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)) := sorry

/-- Any morphism from `R` to the residue field equals `residueHom R`. -/
theorem eq_residueHom (R : CompleteLocalAlgCat Λ k)
    (f : R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) :
    f = residueHom R := sorry

/-- There is a unique morphism `R ⟶ inclusion.obj (residue Λ k)`. -/
noncomputable instance instUnique_hom_residue (R : CompleteLocalAlgCat Λ k) :
    Unique (R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) where
  default := residueHom R
  uniq := sorry

end CompleteLocalAlgCat

