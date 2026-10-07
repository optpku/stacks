module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_25_5_Surjective

/-!
# Descent of flat morphisms of algebraic stacks along surjective flat base change

If the base change of a morphism of algebraic stacks along a surjective flat
morphism is flat, then the original morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Flat

/-- Lemma 101.25.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective flat morphism of algebraic stacks. If the base
change `TwoFibreProduct.snd f g` is flat, then `f` is flat.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06PZ]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Flat f :=
  sorry

/-- Flatness of a morphism of algebraic stacks follows from flatness of the
second projection of a bilimit `PseudoPullbackCone` against a surjective
flat morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g] [Flat g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Flat c.snd] :
    Flat f :=
  sorry

/-- After base change along a surjective flat morphism of algebraic stacks,
the original morphism is flat if and only if `TwoFibreProduct.snd f g` is
flat. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Flat
