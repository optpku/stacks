/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

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

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicStacks

/-- The 2-fibre product of algebraic stacks over `S` in the 2-category
`AlgebraicStacks S`. -/
def twoFibreProduct {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) : AlgebraicStacks S :=
  of (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f.hom g.hom)

namespace twoFibreProduct

/-- Packaging the 2-fibre product in `AlgebraicStacks` forgets to the 2-fibre
product of the underlying groupoid fibrations. -/
theorem toGroupoids {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    AlgebraicStacks.toGroupoids (twoFibreProduct f g) =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f.hom g.hom :=
  sorry

/-- The first projection of a 2-fibre product of algebraic stacks. -/
def fst {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    twoFibreProduct f g ⟶ X :=
  Bicategory.InducedBicategory.mkHom
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f.hom g.hom)

/-- The ambient 1-morphism of `fst` is the first projection of the 2-fibre product. -/
theorem fst_hom {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (fst f g).hom = TwoFibreProduct.fst.{u + 1, u, u + 1, u} f.hom g.hom :=
  sorry

/-- The second projection of a 2-fibre product of algebraic stacks. -/
def snd {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    twoFibreProduct f g ⟶ Y :=
  Bicategory.InducedBicategory.mkHom
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f.hom g.hom)

/-- The ambient 1-morphism of `snd` is the second projection of the 2-fibre product. -/
theorem snd_hom {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (snd f g).hom = TwoFibreProduct.snd.{u + 1, u, u + 1, u} f.hom g.hom :=
  sorry

/-- The canonical 2-isomorphism witnessing 2-commutativity of the 2-fibre-product
square in `AlgebraicStacks S`. -/
def comparisonIso {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    fst f g ≫ f ≅ snd f g ≫ g :=
  Bicategory.InducedBicategory.isoMk
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f.hom g.hom)

/-- The ambient forward 2-morphism of `comparisonIso` is the comparison cell of
the 2-fibre product of groupoid fibrations. -/
theorem comparisonIso.hom {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (comparisonIso f g).hom.hom =
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f.hom g.hom).hom :=
  sorry

/-- The canonical 2-fibre-product cone of `f` and `g` in `AlgebraicStacks S`. -/
def cone {S : Scheme.{u}} {X Y Z : AlgebraicStacks S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PseudoPullbackCone f g where
  pt := twoFibreProduct f g
  fst := fst f g
  snd := snd f g
  iso := comparisonIso f g

/-- The 2-fibre product of algebraic stacks is a 2-fibre product in the
2-category `AlgebraicStacks S`. -/
instance cone.isBilimit {S : Scheme.{u}} {X Y Z : AlgebraicStacks S}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cone f g).IsBilimit :=
  sorry

end twoFibreProduct

end AlgebraicStacks

end AlgebraicGeometry
