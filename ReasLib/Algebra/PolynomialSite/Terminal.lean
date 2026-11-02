/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Terminal identity objects for polynomial algebras

For a polynomial algebra, the identity augmentation is terminal in the polynomial
over-category and in the presheaf indexing category of its opposite site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace Algebra.PolynomialOver

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

/-- The identity object `B ⟶ B` in the category of polynomial `A`-algebra maps to `B`. -/
def idObj : PolynomialOver A B where
  obj := Over.mk (𝟙 (CommAlgCat.of A B))
  property := (inferInstance : IsPolynomial A B)

/-- The underlying over-object of `idObj` is the identity morphism of `CommAlgCat.of A B`. -/
theorem idObj_obj : (idObj A B).obj = Over.mk (𝟙 (CommAlgCat.of A B)) :=
  rfl

/-- The unique morphism from an object `X` of `PolynomialOver A B` to the identity object,
given by the structure map of `X`. -/
def idHom {X : PolynomialOver A B} : X ⟶ idObj A B :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (Category.comp_id X.obj.hom))

/-- The underlying `A`-algebra map of `idHom` is the structure morphism of `X`. -/
theorem idHom_left (X : PolynomialOver A B) :
    (idHom A B : X ⟶ idObj A B).hom.left = X.obj.hom :=
  rfl

/-- The identity object `B ⟶ B` is terminal in `PolynomialOver A B`. -/
def idObj_isTerminal : IsTerminal (idObj A B) :=
  IsTerminal.ofUniqueHom (fun X ↦ idHom A B) (fun _ _ ↦ by
    apply ObjectProperty.hom_ext
    exact (Over.mkIdTerminal (X := CommAlgCat.of A B)).hom_ext _ _)

/-- Maps into the identity object of `PolynomialOver A B` are unique. -/
theorem idObj_isTerminal_unique {X : PolynomialOver A B} (f : X ⟶ idObj A B) :
    f = (idObj_isTerminal A B).from X :=
  (idObj_isTerminal A B).hom_ext _ _

end Algebra.PolynomialOver

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

/-- The identity object `B ⟶ B` as an object of the opposite polynomial site. -/
def idObj : PolynomialSite A B :=
  op (PolynomialOver.idObj A B)

/-- Forgetting the opposite recovers the identity object of `PolynomialOver A B`. -/
theorem idObj_unop : (idObj A B).unop = PolynomialOver.idObj A B :=
  rfl

/-- The identity object `B ⟶ B` in the presheaf indexing category
`(PolynomialSite A B)ᵒᵖ`. -/
def evalObj : (PolynomialSite A B)ᵒᵖ :=
  op (idObj A B)

/-- Forgetting the opposite recovers the identity object of `PolynomialSite A B`. -/
theorem evalObj_unop : (evalObj A B).unop = idObj A B :=
  rfl

/-- The identity object is terminal in `(PolynomialSite A B)ᵒᵖ`. -/
def evalObj_isTerminal : IsTerminal (evalObj A B) :=
  terminalOpOfInitial (initialOpOfTerminal (PolynomialOver.idObj_isTerminal A B))

/-- Maps into the identity object of `(PolynomialSite A B)ᵒᵖ` are unique. -/
theorem evalObj_isTerminal_unique {X : (PolynomialSite A B)ᵒᵖ} (f : X ⟶ evalObj A B) :
    f = (evalObj_isTerminal A B).from X :=
  (evalObj_isTerminal A B).hom_ext _ _

end Algebra.PolynomialSite
