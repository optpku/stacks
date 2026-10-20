/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A pseudo-coherent morphism of algebraic spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_pseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [PseudoCoherent f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
