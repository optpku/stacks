/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation

/-!
# Base change of finite presentation morphisms of algebraic stacks

Morphisms of algebraic stacks of finite presentation, and morphisms that
are locally of finite presentation, remain so along the second projection of
any bilimit 2-fibre product cone, and along the first projection of a chosen
2-fibre product when that leg has the corresponding property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FinitePresentation

/-- Morphisms of algebraic stacks of finite presentation remain of finite
presentation along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [FinitePresentation f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    FinitePresentation c.snd := sorry

/-- The first projection of a chosen 2-fibre product is of finite presentation
whenever the second leg is a finitely presented morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [FinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    FinitePresentation (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.FinitePresentation

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Morphisms of algebraic stacks that are locally of finite presentation
remain so along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [LocallyOfFinitePresentation f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    LocallyOfFinitePresentation c.snd := sorry

/-- The first projection of a chosen 2-fibre product is locally of finite
presentation whenever the second leg is locally of finite presentation. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFinitePresentation
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
