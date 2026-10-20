/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleAdjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 59.100.7: for every scheme and bounded-below complex of abelian small-étale
sheaves, the canonical derived adjunction unit is an isomorphism. -/
@[stacks 0DDT] #check (AlgebraicGeometry.Scheme.FppfEtale.plusAAdjunction_unit_isIso :
  ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
    IsIso ((AlgebraicGeometry.Scheme.FppfEtale.plusAAdjunction X).unit.app K))

end
