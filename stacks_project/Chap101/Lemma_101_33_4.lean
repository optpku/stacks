module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Descent of smoothness for morphisms of algebraic stacks

If the base change of a morphism of algebraic stacks along a surjective, flat,
locally of finite presentation morphism is smooth, then the original morphism
is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- Lemma 101.33.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective, flat, locally of finite presentation morphism of
algebraic stacks. If the base change `TwoFibreProduct.snd f g` is smooth, then
`f` is smooth.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0DN7]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Smooth f :=
  sorry

/-- Smoothness of a morphism of algebraic stacks follows from smoothness of the
second projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally of finite presentation morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Smooth c.snd] :
    Smooth f :=
  sorry

/-- After base change along a surjective, flat, locally of finite presentation
morphism of algebraic stacks, the original morphism is smooth if and only if
`TwoFibreProduct.snd f g` is smooth. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
