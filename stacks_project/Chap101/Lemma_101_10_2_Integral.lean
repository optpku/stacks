/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_10_1_Integral

/-!
# Base change of integral and finite morphisms of algebraic stacks

Integral and finite morphisms of algebraic stacks remain integral, respectively
finite, along the first projection of any bilimit 2-fibre product cone against
an integral, respectively finite, morphism, and along the second projection of
a chosen 2-fibre product when that leg is integral, respectively finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsIntegralHom

/-- Integral morphisms of algebraic stacks remain integral along the first
projection of any bilimit `PseudoPullbackCone` of an arbitrary morphism against
an integral morphism. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [IsIntegralHom g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsIntegralHom c.fst :=
  sorry

/-- The second projection of a chosen 2-fibre product is integral whenever the
first leg is an integral morphism of algebraic stacks. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsIntegralHom (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsIntegralHom

namespace AlgebraicGeometry.AlgebraicStack.IsFinite

/-- Finite morphisms of algebraic stacks remain finite along the first
projection of any bilimit `PseudoPullbackCone` of an arbitrary morphism against
a finite morphism. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [IsFinite g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsFinite c.fst :=
  sorry

/-- The second projection of a chosen 2-fibre product is finite whenever the
first leg is a finite morphism of algebraic stacks. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsFinite (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsFinite
