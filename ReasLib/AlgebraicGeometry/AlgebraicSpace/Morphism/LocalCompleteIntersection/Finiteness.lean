/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness

/-!
# Finiteness properties of local complete intersection morphisms of algebraic spaces

A local complete intersection morphism of algebraic spaces is locally of
finite presentation, pseudo-coherent, and perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A local complete intersection morphism of algebraic spaces is locally of
finite presentation. -/
instance IsLocalCompleteIntersection.locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] : LocallyOfFinitePresentation f :=
  sorry

/-- A local complete intersection morphism of algebraic spaces is
pseudo-coherent. -/
instance IsLocalCompleteIntersection.pseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f] :
    PseudoCoherent f :=
  sorry

/-- A local complete intersection morphism of algebraic spaces is perfect. -/
instance IsLocalCompleteIntersection.perfect {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f] :
    Perfect f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
