module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective

/-!
# Descent of local finite presentation for morphisms of algebraic stacks

If the base change of a morphism of algebraic stacks along a surjective, flat,
locally of finite presentation morphism is locally of finite presentation, then
the original morphism is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Lemma 101.27.11: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective, flat, locally of finite presentation morphism of
algebraic stacks. If the base change `TwoFibreProduct.snd f g` is locally of
finite presentation, then `f` is locally of finite presentation.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06Q8]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFinitePresentation f :=
  sorry

/-- Local finite presentation of a morphism of algebraic stacks follows from
local finite presentation of the second projection of a bilimit
`PseudoPullbackCone` against a surjective, flat, locally of finite presentation
morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFinitePresentation c.snd] :
    LocallyOfFinitePresentation f :=
  sorry

/-- After base change along a surjective, flat, locally of finite presentation
morphism of algebraic stacks, the original morphism is locally of finite
presentation if and only if `TwoFibreProduct.snd f g` is locally of finite
presentation. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔
      LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
