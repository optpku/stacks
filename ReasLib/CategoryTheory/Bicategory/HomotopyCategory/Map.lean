/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the homotopy category

Pseudofunctors to locally discrete targets descend to ordinary functors, and arbitrary
pseudofunctors induce functors between homotopy categories.
-/

@[expose] public section

universe wB vB uB wC vC uC wE vE uE vD uD

namespace CategoryTheory

open scoped Bicategory

section LiftImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Bicategory.HomotopyCategory.Implementation

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Category.{vD} D]

/-- The map on a hom-set obtained by descending a locally discrete pseudofunctor along homwise
connected components. -/
private def liftMap
    (F : B ⥤ᵖ LocallyDiscrete D) {X Y : Bicategory.HomotopyCategory B} :
    (X ⟶ Y) → ((F.obj X.as).as ⟶ (F.obj Y.as).as) :=
  ConnectedComponents.liftFunctor (X.as ⟶ Y.as) (F.mapFunctor X.as Y.as)

/-- Descending sends a represented class to the image of its representative. -/
@[simp]
private theorem liftMap_mkHom
    (F : B ⥤ᵖ LocallyDiscrete D) {X Y : B} (f : X ⟶ Y) :
    liftMap F (Bicategory.HomotopyCategory.mkHom f) = (F.map f).as := sorry

/-- The descended hom-map preserves identities. -/
private theorem liftMap_id
    (F : B ⥤ᵖ LocallyDiscrete D) (X : Bicategory.HomotopyCategory B) :
    liftMap F (𝟙 X) = 𝟙 (F.obj X.as).as := sorry

/-- The descended hom-map preserves composition. -/
private theorem liftMap_comp
    (F : B ⥤ᵖ LocallyDiscrete D)
    {X Y Z : Bicategory.HomotopyCategory B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftMap F (f ≫ g) = liftMap F f ≫ liftMap F g := sorry

end Bicategory.HomotopyCategory.Implementation

namespace Bicategory.HomotopyCategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Category.{vD} D]

/-- A pseudofunctor to a locally discrete bicategory canonically descends to an ordinary functor
from the homotopy `1`-category. -/
@[stacks 04SC "lift through the homotopy-category quotient"]
def lift (F : B ⥤ᵖ LocallyDiscrete D) :
    Bicategory.HomotopyCategory B ⥤ D where
  obj X := (F.obj X.as).as
  map f := Implementation.liftMap F f
  map_id X := Implementation.liftMap_id F X
  map_comp f g := Implementation.liftMap_comp F f g

/-- The descended functor has the original object action on every homotopy-category object. -/
@[simp]
theorem lift.obj (F : B ⥤ᵖ LocallyDiscrete D)
    (X : Bicategory.HomotopyCategory B) :
    (lift F).obj X = (F.obj X.as).as := sorry

/-- The descended functor has the original morphism action on represented homotopy classes. -/
@[simp]
theorem lift.mkHom (F : B ⥤ᵖ LocallyDiscrete D) {X Y : B} (f : X ⟶ Y) :
    (lift F).map (Bicategory.HomotopyCategory.mkHom f) = (F.map f).as := sorry

/-- The descended functor factors the original pseudofunctor through the quotient. -/
@[simp]
theorem lift.fac (F : B ⥤ᵖ LocallyDiscrete D) :
    Pseudofunctor.comp (quotient B) (lift F).toPseudofunctor = F := sorry

/-- A functor with the prescribed factorization through the quotient is the canonical lift. -/
theorem lift.unique (F : B ⥤ᵖ LocallyDiscrete D)
    (G : Bicategory.HomotopyCategory B ⥤ D)
    (fac : Pseudofunctor.comp (quotient B) G.toPseudofunctor = F) :
    G = lift F := sorry

end Bicategory.HomotopyCategory

end LiftImplementation

namespace Bicategory.HomotopyCategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- A pseudofunctor induces an ordinary functor between homotopy categories. -/
@[stacks 04SC "functoriality of the homotopy category"]
def map (F : B ⥤ᵖ C) :
    Bicategory.HomotopyCategory B ⥤ Bicategory.HomotopyCategory C :=
  lift (Pseudofunctor.comp F (quotient C))

namespace map

/-- The induced functor applies the pseudofunctor to the underlying object of any
homotopy-category object. -/
@[simp]
theorem obj (F : B ⥤ᵖ C) (X : Bicategory.HomotopyCategory B) :
    (map F).obj X = Bicategory.HomotopyCategory.mk (F.obj X.as) := sorry

/-- The induced functor sends a represented class to the class of the pseudofunctor image. -/
@[simp]
theorem mkHom (F : B ⥤ᵖ C) {X Y : B} (f : X ⟶ Y) :
    (map F).map (Bicategory.HomotopyCategory.mkHom f) =
      Bicategory.HomotopyCategory.mkHom (F.map f) := sorry

/-- The quotient is natural with respect to the functor induced on homotopy categories. -/
theorem quotient (F : B ⥤ᵖ C) :
    Pseudofunctor.comp (HomotopyCategory.quotient B) (map F).toPseudofunctor =
      Pseudofunctor.comp F (HomotopyCategory.quotient C) := sorry

/-- The identity pseudofunctor induces the identity functor on the homotopy category. -/
@[simp]
theorem id :
    map (Pseudofunctor.id B) = 𝟭 (Bicategory.HomotopyCategory B) := sorry

variable {E : Type uE} [Bicategory.{wE, vE} E]

/-- Passing to homotopy categories preserves composition of pseudofunctors. -/
@[simp]
theorem comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ E) :
    map (Pseudofunctor.comp F G) = map F ⋙ map G := sorry

end map

end Bicategory.HomotopyCategory

end CategoryTheory
