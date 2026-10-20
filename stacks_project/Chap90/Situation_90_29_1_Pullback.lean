/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered

/-!
# Residue-field reindexing of cofibered categories

A finite field extension `k → l` reindexes a functor `p : F ⥤ ArtinianLocalAlgCat Λ k`
along `residueChangeFunctor Λ k l` by categorical pullback. The resulting projection
`residueChangeOver p` is cofibered in groupoids whenever `p` is, and its fibre over `B`
is equivalent to the fibre of `p` over `B ×_l k`.
-/

@[expose] public section

open CategoryTheory Functor Limits
open scoped CategoricalPullback

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.residueChangeOver Λ k l p :
  ArtinianLocalAlgCat.residueChangeTotal Λ k l p ⥤ ArtinianLocalAlgCat Λ l)

#check (ArtinianLocalAlgCat.residueChangeOver.fiberMk Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    p.Fiber ((ArtinianLocalAlgCat.residueChangeFunctor Λ k l).obj B) ⥤
      (ArtinianLocalAlgCat.residueChangeOver Λ k l p).Fiber B)

end ArtinianLocalAlgCat
