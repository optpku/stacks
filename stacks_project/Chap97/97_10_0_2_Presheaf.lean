/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap97.«97_10_0_2_Morphism»

/-!
# Relative-Hom functor of algebraic spaces

The functor `Mor_B(Z, X)` on `(Sch/S)^opp`, sending a scheme `T` over `S` to
the type of pairs `(a, b)` with `a : ofOver T ⟶ B` and `b` a morphism over
`ofOver T` between the fibre products with `Z` and `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

namespace StacksProject.Chap97.RelativeHom

/-- The relative-Hom functor `Mor_B(Z, X)` on schemes over `S`. -/
noncomputable def functor {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := HomPair Z X T.unop
  map f := ofHom fun p ↦ HomPair.pullback f.unop p
  map_id := sorry
  map_comp := sorry

/-- Evaluating the relative-Hom functor at `T` recovers the type of pairs over `T`. -/
theorem functor_obj {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (functor Z X).obj (op T) = HomPair Z X T :=
  sorry

/-- Restriction in the relative-Hom functor is `HomPair.pullback`. -/
theorem functor_map {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T T' : Over S} (f : T' ⟶ T) (p : HomPair Z X T) :
    (functor Z X).map f.op p = HomPair.pullback f p :=
  sorry

end StacksProject.Chap97.RelativeHom
