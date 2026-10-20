/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation

/-!
# Finite-presentation consequences of syntomicity

Syntomic morphisms of algebraic spaces are locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A syntomic morphism of algebraic spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_syntomic {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
