/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue

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

#check (CompleteLocalAlgCat.residueHom : ∀ R : CompleteLocalAlgCat Λ k,
  R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k))

#check (CompleteLocalAlgCat.residueHom_hom : ∀ R : CompleteLocalAlgCat Λ k,
  (residueHom R).hom =
      R.residueFieldIso.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)))

#check (CompleteLocalAlgCat.eq_residueHom : ∀ (R : CompleteLocalAlgCat Λ k)
  (f : R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)),
  f = residueHom R)

#check (CompleteLocalAlgCat.instUnique_hom_residue : ∀ R : CompleteLocalAlgCat Λ k,
  Unique (R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)))

end CompleteLocalAlgCat
