module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-!
# Change-of-base equivalence for algebraic spaces

A morphism `g : S ⟶ S'` induces an equivalence between algebraic spaces over `S` and
objects of `Over (ofOver (Over.mk g))`, i.e. algebraic spaces over `S'` equipped with a
morphism to `S` over `S'`. The forward functor is `j_!` together with the canonical
structure morphism; the inverse is the Type `u` fiber of that structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.extendBaseOver :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S'),
    AlgebraicSpace S ⥤ Over (ofOver (Over.mk g)))

#check (AlgebraicGeometry.AlgebraicSpace.restrictOverFunctor :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S'),
    Over (ofOver (Over.mk g)) ⥤ AlgebraicSpace S)

end AlgebraicGeometry.AlgebraicSpace
