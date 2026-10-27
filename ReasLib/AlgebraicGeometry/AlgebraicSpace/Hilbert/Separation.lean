/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Separation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Hilbert functor of a separated morphism of finite presentation between
algebraic spaces is separated over the base. -/
instance instIsSeparatedOver (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    Quot.IsSeparatedOver (hilbert f) where
  isClosedImmersion_diagonal := Hilbert.isClosedImmersion_diagonal f

end AlgebraicGeometry.AlgebraicSpace.Hilbert
