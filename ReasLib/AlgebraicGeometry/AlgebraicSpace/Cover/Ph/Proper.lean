/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Singleton proper-surjective ph coverings of algebraic spaces

A surjective proper morphism of algebraic spaces, viewed as a singleton family,
is a ph covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective proper morphism of algebraic spaces, regarded as a singleton
family, is a ph covering. -/
instance phCoveringSingletonOfProperSurjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Proper f] [Surjective f] :
    PhCovering (fun _ : PUnit ↦ Y) (fun _ ↦ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
