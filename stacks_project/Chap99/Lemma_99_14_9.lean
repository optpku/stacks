/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Thickening
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap99.Lemma_99_14_9_Restrict

/-!
# Lemma 99.14.9

Restriction of Polarized fibre categories along a pushout square of schemes
whose vertical arrow is a thickening and whose horizontal arrow is affine is
an equivalence, by More on Morphisms, Lemma 37.14.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

variable {T T' S S' : Scheme.{u}}

/-- The categorical square of Polarized fibre restrictions around a pushout of
schemes. -/
def toPullbackSquare (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) :
    CategoricalPullback.CatCommSqOver (restrict f) (restrict i) (p.Fiber S') where
  fst := restrict h
  snd := restrict g
  iso :=
    (restrict_comp f h).symm ≪≫
      eqToIso (congrArg restrict H.w.symm) ≪≫ restrict_comp i g

/-- The functor on Polarized fibre categories
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
  sorry

/-- The second component of `toPullback` is restriction along `T' ⟶ S'`. -/
theorem toPullback_obj_snd (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (H : IsPushout i f g h) (x : p.Fiber S') :
    ((toPullback i f g h H).obj x).snd = (restrict g).obj x :=
  sorry

/-- The comparison functor on the canonical pushout of a thickening and an affine
morphism. -/
def toPullback_pushout (i : T ⟶ T') (f : T ⟶ S) [IsThickening i] [IsAffineHom f] :
    p.Fiber (pushout i f) ⥤ ((restrict f) ⊡ (restrict i)) :=
  toPullback i f (pushout.inl i f) (pushout.inr i f) (IsPushout.of_hasPushout i f)

/-- Lemma 99.14.9: if `T ⟶ T'` is a thickening and `T ⟶ S` is affine, then the
functor `toPullback H` on Polarized fibre categories is an equivalence. -/
@[stacks 0D44, instance]
instance toPullback_isEquivalence (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    [IsThickening i] [IsAffineHom f] (H : IsPushout i f g h) :
    (toPullback i f g h H).IsEquivalence :=
  sorry

end AlgebraicGeometry.Polarized
