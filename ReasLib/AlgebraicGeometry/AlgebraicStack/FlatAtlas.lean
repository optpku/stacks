/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Bootstrapping algebraic stacks from an fppf algebraic-space atlas

A stack in groupoids admitting a representable, surjective, flat, locally
finitely presented morphism from an algebraic space is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `X` is representable by an
algebraic space, and `F` is representable by algebraic spaces, surjective,
flat and locally of finite presentation, then `Y` is an algebraic stack. The
hypotheses `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`, and
`Groupoids.Hom.LocallyOfFinitePresentation` each include
`relativelyRepresentableByAlgebraicSpaces F`. -/
@[stacks 06DC]
theorem of_fppfAtlas {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (hX : IsRepresentableByAlgebraicSpace X)
    [Groupoids.Hom.Surjective F] [Groupoids.Hom.Flat F]
    [Groupoids.Hom.LocallyOfFinitePresentation F] :
    AlgebraicStack Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
