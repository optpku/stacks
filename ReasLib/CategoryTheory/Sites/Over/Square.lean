/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Squares of slice-site pullback functors

A commutative square in a category induces a square of slice reindexing functors and hence a
square of continuous pullback functors on sheaves.  Cartesian squares are Guitart exact.  These
owners are independent of any direct-image or Beck--Chevalley construction.
-/

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

namespace Over

variable {C : Type u} [Category.{v} C]
variable {U' U V' V : C}

/-- A commutative square induces a `2`-commutative square of slice reindexing functors. -/
@[stacks 0EYV "slice reindexing square", implicit_reducible]
noncomputable def mapCommSq
    (i : U' ⟶ U) (p : U' ⟶ V') (f : U ⟶ V) (g : V' ⟶ V)
    (hcomm : i ≫ f = p ≫ g) :
    CatCommSq (Over.map i) (Over.map p) (Over.map f) (Over.map g) where
  iso := (Over.mapComp i f).symm ≪≫
    Over.mapCongr (i ≫ f) (p ≫ g) hcomm ≪≫
      Over.mapComp p g

/-- A cartesian square induces a Guitart-exact square of slice reindexing functors. -/
@[stacks 0EYV "Guitart exactness of a cartesian slice square"]
theorem mapCommSq_guitartExact_of_isPullback
    (i : U' ⟶ U) (p : U' ⟶ V') (f : U ⟶ V) (g : V' ⟶ V)
    (hcart : IsPullback i p f g) :
    TwoSquare.GuitartExact (Over.mapCommSq i p f g hcart.w).iso.hom := sorry

end Over

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U' U V' V : C}

/-- Pullback functors on `A`-valued sheaves over slices form the square induced by a commutative
square in the base category. -/
@[stacks 0EYV "pullback square on slice sheaves"]
noncomputable def overMapPullbackSquare
    (A : Type w) [Category A]
    (i : U' ⟶ U) (p : U' ⟶ V') (f : U ⟶ V) (g : V' ⟶ V)
    (hcomm : i ≫ f = p ≫ g) :
    J.overMapPullback A f ⋙ J.overMapPullback A i ≅
      J.overMapPullback A g ⋙ J.overMapPullback A p :=
  J.overMapPullbackComp A i f ≪≫
    J.overMapPullbackCongr A hcomm ≪≫
      (J.overMapPullbackComp A p g).symm

end GrothendieckTopology

end CategoryTheory

end
