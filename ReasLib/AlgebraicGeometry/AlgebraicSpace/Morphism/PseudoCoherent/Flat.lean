/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Flat

/-!
# Pseudo-coherence of flat algebraic-space morphisms locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat morphism of algebraic spaces which is locally of finite presentation
is pseudo-coherent. -/
instance pseudoCoherent_of_flat_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] : PseudoCoherent f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
