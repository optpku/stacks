/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- 63.4.0.1: for a locally quasi-finite morphism `f : X ⟶ Y`, an abelian sheaf
`F` on `X_étale`, and `V` in `Y_étale`, a typical finite formal sum is
`s = ∑ i, FreeAbelianGroup.of (t i)`, where each `t i : FiniteSupportTerm f F V`
is a pair `(Z_i, s_i)` with `Z_i ⊂ X_V` a locally closed subscheme finite over
`V` and `s_i ∈ H_{Z_i}(F)`. -/
@[stacks 0F6J] #check (AlgebraicGeometry.Scheme.Etale.FiniteSupportFormalSum.sum :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} {V : Y.Etale} {n : ℕ},
    (Fin n → AlgebraicGeometry.Scheme.Etale.FiniteSupportTerm f F V) →
      AlgebraicGeometry.Scheme.Etale.FiniteSupportFormalSum f F V)

end
