/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow

@[expose] public section

open CategoryTheory

universe u

/- Definition 111.35.3: for a morphism of schemes `f : X ⟶ S` and a point `x : X`,
the type `DottedTangentArrow f x` of dotted arrows in the solid dual-number square
is the tangent space of `X` over `S` at `x`, denoted `T_{X/S, x}`. An element of this
space is called a tangent vector of `X/S` at `x`. -/
@[stacks 029F] #check (AlgebraicGeometry.Scheme.Hom.DottedTangentArrow :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X), Type u)
