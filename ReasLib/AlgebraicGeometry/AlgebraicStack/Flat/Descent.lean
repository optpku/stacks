module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Descent of flatness for morphisms of algebraic stacks

Flatness descends through flat surjective morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Flat

/-- For composable morphisms of algebraic stacks, flatness of the composite
and flatness and surjectivity of the first morphism imply flatness of the second. -/
theorem of_comp_surjective_flat {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Flat (f ≫ g)] [AlgebraicStack.Flat f]
    [AlgebraicStack.Surjective f] : AlgebraicStack.Flat g :=
  sorry

/-- A morphism of algebraic stacks is flat if its base change along a
surjective flat morphism is flat. -/
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g]
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
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g] :
    Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Flat f :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
