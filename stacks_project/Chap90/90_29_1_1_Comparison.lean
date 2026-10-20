/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange

/-!
# Residue-field change for `ArtinianLocalAlgCat`

A finite field extension `k → l` induces a comparison functor
`ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k` sending `B` to the
algebra fibre product of `toResidue B` along `k → l`.
-/

@[expose] public section

open CategoryTheory

universe u

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

/- The comparison functor is the canonical residue-change construction. -/
#check (ArtinianLocalAlgCat.residueChangeFunctor Λ k l :
  ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k)

/- The first projection is a Λ-algebra map to the original object. -/
#check (ArtinianLocalAlgCat.residueChangeFst k :
  (B : ArtinianLocalAlgCat Λ l) → (ArtinianLocalAlgCat.residueChange k B).carrier →ₐ[Λ] B.carrier)
