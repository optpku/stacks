/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace

/-! # Algebraic space associated to an étale sheaf of sets -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.27.3 (1): the pair functor of an étale sheaf defines an algebraic space
under the set-theoretic smallness hypothesis. -/
#check (AlgebraicGeometry.AlgebraicSpace.sheafSpace :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F),
    AlgebraicSpace S)
