/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Bicategory.StrictSlice
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory

/-!
# Algebraic stacks over a slice algebraic stack

A morphism `g : S ⟶ S'` of the big fppf site determines the algebraic stack
`(Sch/S)_fppf` over `S'`, namely the canonical slice of `Over.mk g`. Pairs
`(X', f)` consisting of an algebraic stack over `S'` and a morphism
`f : X' ⟶ (Sch/S)_fppf` are objects of the strict slice of that algebraic
stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStacks

/-- The algebraic stack `(Sch/S)_fppf` over `S'`, obtained by viewing the
canonical slice of `S` over `S'` as an algebraic stack. -/
def overSlice {S S' : Scheme.{u}} (g : S ⟶ S') : AlgebraicStacks S' :=
  of (GroupoidsOver.slice (Over.mk g))

/-- `overSlice g` is the algebraic stack associated to the canonical slice of
`Over.mk g`. -/
theorem overSlice_eq {S S' : Scheme.{u}} (g : S ⟶ S') :
    overSlice g = of (GroupoidsOver.slice (Over.mk g)) :=
  sorry

/-- The underlying groupoid fibration of `overSlice g` is the canonical slice of
`S` over `S'`. -/
theorem overSlice_toGroupoids {S S' : Scheme.{u}} (g : S ⟶ S') :
    toGroupoids (overSlice g) = GroupoidsOver.slice (Over.mk g) :=
  sorry

/-- The 2-category of pairs `(X', f)` consisting of an algebraic stack `X'` over
`S'` and a morphism `f : X' ⟶ overSlice g` of algebraic stacks over `S'`. -/
abbrev OverSlice {S S' : Scheme.{u}} (g : S ⟶ S') :=
  Bicategory.StrictSlice (overSlice g)

namespace OverSlice

/-- Package an algebraic stack over `S'` with a morphism to `overSlice g` as an
object of the pair 2-category. -/
def mk {S S' : Scheme.{u}} {g : S ⟶ S'} (X' : AlgebraicStacks S')
    (f : X' ⟶ overSlice g) : OverSlice g :=
  Bicategory.StrictSlice.mk X' f

/-- The algebraic stack over `S'` underlying a pair. -/
abbrev obj {S S' : Scheme.{u}} {g : S ⟶ S'} (P : OverSlice g) : AlgebraicStacks S' :=
  Bicategory.StrictSlice.obj P

/-- The structural morphism of a pair, landing in `overSlice g`. -/
abbrev hom {S S' : Scheme.{u}} {g : S ⟶ S'} (P : OverSlice g) : obj P ⟶ overSlice g :=
  Bicategory.StrictSlice.hom P

/-- The domain of a constructed pair is the supplied algebraic stack. -/
@[simp]
theorem mk_obj {S S' : Scheme.{u}} {g : S ⟶ S'} (X' : AlgebraicStacks S')
    (f : X' ⟶ overSlice g) : (mk X' f).obj = X' :=
  sorry

/-- The structural morphism of a constructed pair is the supplied morphism. -/
@[simp]
theorem mk_hom {S S' : Scheme.{u}} {g : S ⟶ S'} (X' : AlgebraicStacks S')
    (f : X' ⟶ overSlice g) : (mk X' f).hom = f :=
  sorry

/-- Reconstructing a pair from its domain and structural morphism recovers the
original object. -/
theorem mk_eta {S S' : Scheme.{u}} {g : S ⟶ S'} (P : OverSlice g) :
    mk P.obj P.hom = P :=
  sorry

/-- Objects of `OverSlice g` are pairs consisting of an algebraic stack over `S'`
and a morphism to `overSlice g`. -/
theorem iff_mk {S S' : Scheme.{u}} {g : S ⟶ S'} (P : OverSlice g) :
    ∃ (X' : AlgebraicStacks S') (f : X' ⟶ overSlice g), P = mk X' f :=
  sorry

end OverSlice

end AlgebraicGeometry.AlgebraicStacks
