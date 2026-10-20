/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Remark 42.33.5: restriction along a locally finite-type cartesian base-change square sends
a degree-`p` bivariant class to a degree-`p` bivariant class. -/
@[stacks 0F9Z] #check (AlgebraicGeometry.BivariantClass.restrict :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ),
    BivariantClass delta f p → BivariantClass delta f' p)

/- The cap action of a restriction is the original cap action on the pasted square. -/
#check (AlgebraicGeometry.BivariantClass.restrict_apply :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (p : ℤ)
    (c : BivariantClass delta f p)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [LocallyOfFiniteType h.left]
    (inner : IsPullback j.left f''.left f'.left h.left) (k : ℤ)
    (alpha : RelativeChow delta Y'' k),
    (BivariantClass.restrict delta i f' g square p c).cap j f'' h inner k alpha =
      c.cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz square) k alpha)

/- Successive restrictions agree with restriction along the pasted cartesian square. -/
#check (AlgebraicGeometry.BivariantClass.restrict_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    {f : X ⟶ Y} (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    [LocallyOfFiniteType h.left]
    (inner : IsPullback j.left f''.left f'.left h.left) (p : ℤ)
    (c : BivariantClass delta f p),
    BivariantClass.restrict delta j f'' h inner p
        (BivariantClass.restrict delta i f' g square p c) =
      BivariantClass.restrict delta (j ≫ i) f'' (h ≫ g)
        (inner.paste_horiz square) p c)
