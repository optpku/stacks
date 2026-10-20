module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective.BaseChange

/-!
# Descent of surjectivity for morphisms of algebraic stacks

Surjectivity descends after base change along a surjective morphism of
algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Surjective

/-- For a bilimit cone of morphisms of algebraic stacks, surjectivity of the
second projection and of the second leg implies surjectivity of the first leg. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Surjective c.snd] : Surjective f :=
  sorry

/-- If the first leg and first projection of a chosen 2-fibre product of
algebraic stacks are surjective, then the second leg is surjective. -/
theorem of_twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective f]
    [Surjective (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)] :
    Surjective g :=
  sorry

/-- For a bilimit cone of morphisms of algebraic stacks with surjective second
leg, the second projection is surjective if and only if the first leg is. -/
theorem isBilimit_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    Surjective c.snd ↔ Surjective f :=
  sorry

/-- A morphism of algebraic stacks is surjective if its base change along a
surjective morphism is surjective. -/
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g]
    [Surjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Surjective f :=
  sorry

/-- After base change along a surjective morphism of algebraic stacks, the
second projection is surjective if and only if the original morphism is. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] :
    Surjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Surjective f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Surjective
