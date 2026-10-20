/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct.Bicategory
import StacksCheckRecall

/-!
# 2-fibre products of algebraic stacks

If `X`, `Y`, `Z` are algebraic stacks over a scheme `S` and `f : X ⟶ Z`,
`g : Y ⟶ Z` are 1-morphisms, then the 2-fibre product of `f` and `g` is an
algebraic stack, and is a 2-fibre product in the 2-category of algebraic stacks
over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 94.14.3: the canonical 2-fibre product of algebraic stacks is algebraic. -/
@[stacks 04T2]
#check (AlgebraicGeometry.AlgebraicStack.instTwoFibreProduct :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Z} {g : Y ⟶ Z},
    AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    AlgebraicStacks S)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.toGroupoids :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    AlgebraicStacks.toGroupoids (AlgebraicStacks.twoFibreProduct f g) =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f.hom g.hom)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.fst :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    AlgebraicStacks.twoFibreProduct f g ⟶ X)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.fst_hom :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    (AlgebraicStacks.twoFibreProduct.fst f g).hom =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f.hom g.hom)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    AlgebraicStacks.twoFibreProduct f g ⟶ Y)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.snd_hom :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    (AlgebraicStacks.twoFibreProduct.snd f g).hom =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f.hom g.hom)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.comparisonIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    AlgebraicStacks.twoFibreProduct.fst f g ≫ f ≅
      AlgebraicStacks.twoFibreProduct.snd f g ≫ g)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.comparisonIso.hom :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    (AlgebraicStacks.twoFibreProduct.comparisonIso f g).hom.hom =
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f.hom g.hom).hom)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.cone :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    PseudoPullbackCone f g)

#check (AlgebraicGeometry.AlgebraicStacks.twoFibreProduct.cone.isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z),
    (AlgebraicStacks.twoFibreProduct.cone f g).IsBilimit)

