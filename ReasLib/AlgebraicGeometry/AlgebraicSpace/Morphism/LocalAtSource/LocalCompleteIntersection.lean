/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage

/-!
# Syntomic source-locality of local complete intersection morphisms

Local complete intersection morphisms of algebraic spaces are local on the
source for the syntomic precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/-- Local complete intersection morphisms of algebraic spaces are local on the
source for the syntomic precoverage. -/
instance isLocalAtSourceSyntomic {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection
