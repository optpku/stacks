/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Polarized.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Thickening
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Polarized families over pushouts of schemes

Restriction of polarized families around a pushout square gives a comparison
functor to the categorical pullback of the fibre categories. This functor is an
equivalence when the top horizontal morphism is a thickening and the left
vertical morphism is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

variable {T T' S S' : Scheme.{u}}

/-- The categorical square of polarized fibre restrictions around a pushout of
schemes. -/
def toPullbackSquare (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) :
    CategoricalPullback.CatCommSqOver (restrict f) (restrict i) (p.Fiber S') where
  fst := restrict h
  snd := restrict g
  iso :=
    (restrict_comp f h).symm ≪≫
      eqToIso (congrArg restrict H.w.symm) ≪≫ restrict_comp i g

/-- The functor on polarized fibre categories
`p.Fiber S' ⥤ ((restrict f) ⊡ (restrict i))` associated to a pushout square of
schemes. -/
@[stacks 0D44]
def toPullback (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) :
    p.Fiber S' ⥤ ((restrict f) ⊡ (restrict i)) :=
  (toPullbackSquare i f g h H).comparison

/-- The first component of `toPullback` is restriction along `S ⟶ S'`. -/
theorem toPullback_obj_fst (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) (x : p.Fiber S') :
    ((toPullback i f g h H).obj x).fst = (restrict h).obj x :=
  rfl

/-- The second component of `toPullback` is restriction along `T' ⟶ S'`. -/
theorem toPullback_obj_snd (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) (x : p.Fiber S') :
    ((toPullback i f g h H).obj x).snd = (restrict g).obj x :=
  rfl

/-- The comparison functor on the canonical pushout of a thickening and an affine
morphism. -/
def toPullback_pushout (i : T ⟶ T') (f : T ⟶ S) [IsThickening i] [IsAffineHom f] :
    p.Fiber (pushout i f) ⥤ ((restrict f) ⊡ (restrict i)) :=
  toPullback i f (pushout.inl i f) (pushout.inr i f) (IsPushout.of_hasPushout i f)

/-- Restriction of polarized families over a pushout of a thickening `T ⟶ T'`
and an affine morphism `T ⟶ S` is an equivalence of categories. -/
@[stacks 0D44, instance]
instance toPullback_isEquivalence (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    [IsThickening i] [IsAffineHom f] (H : IsPushout i f g h) :
    (toPullback i f g h H).IsEquivalence :=
  sorry

end AlgebraicGeometry.Polarized
