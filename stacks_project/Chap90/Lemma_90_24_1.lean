/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.RimSchlessinger

/-!
# Rim-Schlessinger for quotients of smooth groupoids in functors

If `(U, R, s, t, c)` is a smooth groupoid in functors on `ArtinianLocalAlgCat Λ k`
and the set-valued functors `U` and `R` satisfy (RS), then the quotient category
cofibered in groupoids `[U/R]` satisfies (RS).
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/- Lemma 90.24.1: if `(U, R, s, t, c)` is a smooth groupoid in functors on
`ArtinianLocalAlgCat Λ k` and the set-valued functors `U` and `R` satisfy (RS), then
the quotient category cofibered in groupoids `[U/R]` satisfies (RS). -/
@[stacks 06KT] #check (CategoryTheory.GroupoidInFunctors.hasRimSchlessinger_quotient :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    [CategoryTheory.GroupoidInFunctors.IsSmooth G.s G.t] →
      Functor.HasSchlessingerH4 G.U → Functor.HasSchlessingerH4 G.R →
        Functor.HasRimSchlessinger G.quotient.p)

end CategoryTheory.GroupoidInFunctors
