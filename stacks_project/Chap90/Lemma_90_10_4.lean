/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Along

/-!
# Schlessinger's (S2) along finite square-zero extensions

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (S2),
then both clauses of (S2) remain valid after replacing `dualNumber Λ k` by
`squareZero Λ k V` for every finite `k`-module `V`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/- Lemma 90.10.4: if a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
satisfies (S2), then both clauses of (S2) also hold when `dualNumber Λ k` is replaced
by `squareZero Λ k V` for any finite `k`-module `V`. -/
@[stacks 06HZ]
#check (CategoryTheory.Functor.hasSchlessingerS2Along :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V],
    HasSchlessingerS2Along p V)

end CategoryTheory.Functor
