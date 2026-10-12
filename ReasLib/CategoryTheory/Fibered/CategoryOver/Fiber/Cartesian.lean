/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Action
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian morphisms of fibred categories

This leaf owns preservation readouts and constructors for the cartesian morphisms in
`FiberedCategoryOver C`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w vS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

variable {X Y : FiberedCategoryOver C}

/-- Strongly cartesian morphisms are preserved by a morphism of fibred categories. -/
theorem mapStronglyCartesian
    (F : X ⟶ Y) {a b : X.total} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    Y.p.IsStronglyCartesian (Y.p.map ((toFunctor F).map φ)) ((toFunctor F).map φ) := sorry
/- Proof strategy: unfold `toFunctor`, `toBasedFunctor`, and the locally induced hom property;
apply the stored preservation witness `F.property` to `φ` and `hφ`. -/

/-- A morphism of fibred categories sends a strongly cartesian lift over a specified base
morphism to a strongly cartesian lift over the same base morphism. -/
theorem Map.stronglyCartesianOfLift
    (F : X ⟶ Y) {a b : X.total} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f ((toFunctor F).map φ) := sorry
/- Proof strategy: normalize the displayed base arrow to the owner map, apply
`mapStronglyCartesian`, and transport back through the based-functor compatibility equation. -/

/-- Forget a fixed-universe morphism of fibred categories to its universe-polymorphic cartesian
based functor. This projection exposes the single data owner used by both APIs. -/
def toCartesianBasedFunctor (F : X ⟶ Y) :
    CartesianBasedFunctor X.p Y.p :=
  ⟨toBasedFunctor F, F.property⟩

/-- Coerce an owner morphism to its underlying based functor over `C`. -/
instance coeBasedFunctor : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- Build a morphism of fibred categories from a based functor preserving strongly cartesian
morphisms. -/
def ofBasedFunctor (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hG : G.PreservesStronglyCartesian) : X ⟶ Y :=
  ⟨G, hG⟩

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor.toBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hG : G.PreservesStronglyCartesian) :
    FiberedCategoryOver.toBasedFunctor
      (FiberedCategoryOver.ofBasedFunctor G hG) = G := sorry
/- Proof strategy: unfold `toBasedFunctor` and `ofBasedFunctor`; the locally induced hom
constructor stores `G` as its object field. -/

end FiberedCategoryOver

end CategoryTheory
