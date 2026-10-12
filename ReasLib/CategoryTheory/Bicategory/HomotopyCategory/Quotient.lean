/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# The homotopy-category quotient pseudofunctor

This file packages the homwise connected-component projections into the canonical pseudofunctor
from a bicategory to the locally discrete bicategory on its homotopy category.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory.HomotopyCategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace quotient

/-- The canonical projection from a hom-category to the discrete category on its connected
components. -/
@[stacks 04SC "homwise connected-component quotient"]
def hom (X Y : B) :
    (X ⟶ Y) ⥤ Discrete (ConnectedComponents (X ⟶ Y)) :=
  ConnectedComponents.quotient (X ⟶ Y)

end quotient

variable (B) in
/-- The canonical pseudofunctor from a bicategory to the locally discrete bicategory on its
homotopy `1`-category. The ambient bicategory is explicit because there is no value input from
which Lean could infer it. -/
@[stacks 04SC "homotopy-category quotient pseudofunctor"]
def quotient : B ⥤ᵖ LocallyDiscrete (HomotopyCategory B) where
  __ := PrelaxFunctor.mkOfHomFunctors
    (fun X ↦ LocallyDiscrete.mk (HomotopyCategory.mk X))
    (fun X Y ↦ quotient.hom X Y)
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

/-- The homotopy-category quotient is the identity on objects, viewed in the locally discrete
target bicategory. -/
@[simp]
theorem quotient.obj (X : B) :
    (quotient B).obj X = LocallyDiscrete.mk (HomotopyCategory.mk X) := sorry

/-- The homotopy-category quotient sends a `1`-morphism to its connected-component class. -/
@[simp]
theorem quotient.map {X Y : B} (f : X ⟶ Y) :
    (quotient B).map f = (mkHom f).toLoc := sorry

/-- The homotopy-category quotient sends a `2`-morphism to the equality induced by its
connected-component identification. -/
@[simp]
theorem quotient.map₂ {X Y : B} {f g : X ⟶ Y} (eta : f ⟶ g) :
    (quotient B).map₂ eta = (quotient.hom X Y).map eta := sorry

/-- The homotopy-category quotient has the reflexive identity comparison. -/
@[simp]
theorem quotient.mapId (X : B) :
    (quotient B).mapId X = Iso.refl _ := sorry

/-- The homotopy-category quotient has the reflexive composition comparison. -/
@[simp]
theorem quotient.mapComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (quotient B).mapComp f g = Iso.refl _ := sorry

end CategoryTheory.Bicategory.HomotopyCategory
