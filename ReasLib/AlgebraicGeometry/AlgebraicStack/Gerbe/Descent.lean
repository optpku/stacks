/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Descent of gerbes of algebraic stacks along fppf morphisms

For `f : X ⟶ Y` and a surjective, flat, locally of finite presentation
base-change morphism `g : Z ⟶ Y`, being a gerbe after base change along `g`
implies that `f` is a gerbe over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Gerbe

/-- Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic stacks, and
let `c` be a fibre-product cone. If `g` is surjective, flat, and locally of
finite presentation and `c.snd` makes the apex a gerbe over `Z`, then `X` is
a gerbe over `Y`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] [c.IsBilimit]
    [Gerbe c.snd] :
    Gerbe f :=
  sorry

/-- Being a gerbe over the target of a morphism of algebraic stacks follows
from being a gerbe over the second projection of a chosen 2-fibre product
against a surjective, flat, locally of finite presentation morphism. -/
theorem of_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Gerbe (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Gerbe f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Gerbe
