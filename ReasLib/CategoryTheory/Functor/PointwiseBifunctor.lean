/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Pointwise bifunctors on functor categories

A curried bifunctor acts pointwise on two functor categories with the same source.  This file gives
that construction a short owner and propagates preservation of zero morphisms, which is the
structure needed to totalize the resulting bifunctor on homological complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK vK uA vA uB vB uD vD

namespace CategoryTheory.Functor.PointwiseBifunctor

variable {K : Type uK} [Category.{vK} K]
variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {D : Type uD} [Category.{vD} D]

/-- Apply a curried bifunctor pointwise to two functor categories with the same source. -/
@[stacks 07MB "pointwise bifunctor on functor categories"]
abbrev functor (T : A ⥤ B ⥤ D) : (K ⥤ A) ⥤ (K ⥤ B) ⥤ K ⥤ D :=
  (Functor.whiskeringRight₂ K A B D).obj T

/-- The pointwise value of a curried bifunctor on two functors. -/
@[stacks 07MB "pointwise value of a bifunctor on functors"]
abbrev obj (T : A ⥤ B ⥤ D) (F : K ⥤ A) (G : K ⥤ B) : K ⥤ D :=
  ((functor T).obj F).obj G

/-- The pointwise morphism induced by a morphism in each input functor category. -/
@[stacks 07MB "pointwise morphism induced by a bifunctor"]
def map (T : A ⥤ B ⥤ D) {F F' : K ⥤ A} {G G' : K ⥤ B}
    (f : F ⟶ F') (g : G ⟶ G') : obj T F G ⟶ obj T F' G' :=
  ((functor T).map f).app G ≫ ((functor T).obj F').map g

/-- The component of a pointwise bifunctor map is the bifunctor map of the two components. -/
@[stacks 07MB "component of a pointwise bifunctor morphism"]
theorem map_app (T : A ⥤ B ⥤ D) {F F' : K ⥤ A} {G G' : K ⥤ B}
    (f : F ⟶ F') (g : G ⟶ G') (k : K) :
    (map T f g).app k = (T.map (f.app k)).app (G.obj k) ≫
      (T.obj (F'.obj k)).map (g.app k) := sorry

section ZeroMorphisms

variable [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]

/-- Pointwise application preserves zero morphisms in its first functor variable. -/
@[stacks 07MB "pointwise bifunctor preserves zero morphisms in the first variable"]
instance functorPreservesZeroMorphisms (T : A ⥤ B ⥤ D)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] :
    (functor (K := K) T).PreservesZeroMorphisms := sorry

/-- Pointwise application preserves zero morphisms in its second functor variable. -/
@[stacks 07MB "pointwise bifunctor preserves zero morphisms in the second variable"]
instance objPreservesZeroMorphisms (T : A ⥤ B ⥤ D)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (F : K ⥤ A) : ((functor T).obj F).PreservesZeroMorphisms := sorry

end ZeroMorphisms

end CategoryTheory.Functor.PointwiseBifunctor

end
