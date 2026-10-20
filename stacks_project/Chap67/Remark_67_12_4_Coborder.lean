/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Coborder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Factorization

/-! Compatibility facade for the source coborder factorization. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.exists_closedImmersion_openImmersion_factorization :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [AlgebraicSpace.IsImmersion f],
      ∃ (U : AlgebraicSpace S) (c : Z ⟶ U) (o : U ⟶ X),
        AlgebraicSpace.IsClosedImmersion c ∧ AlgebraicSpace.IsOpenImmersion o ∧ c ≫ o = f)
