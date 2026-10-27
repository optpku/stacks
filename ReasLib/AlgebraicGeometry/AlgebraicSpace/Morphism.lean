/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a morphism of their functors of points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme `S` is a morphism of their functors of
points. -/
abbrev Hom {S : Scheme.{u}} (F F' : AlgebraicSpace S) :=
  F.functorOfPoints ⟶ F'.functorOfPoints

namespace OpenSubspace

noncomputable section

/-- A section of the functor of points over a scheme determines a morphism from
the algebraic space represented by that scheme. -/
abbrev homOfPointsSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : (Over S)ᵒᵖ} (φ : X.functorOfPoints.obj U) :
    ofOver U.unop ⟶ X :=
  yonedaEquiv.symm φ

end

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
