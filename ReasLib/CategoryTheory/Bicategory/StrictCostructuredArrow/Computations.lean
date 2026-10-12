/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictCostructuredArrow.Basic

/-!
# Computations for strict costructured arrows

Readout lemmas for the source maps and source cells of the generic strict
costructured-arrow construction.
-/

@[expose] public section

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace StrictCostructuredArrow

variable [Bicategory.Strict A] [Bicategory.Strict C]
variable {K : StrictPseudofunctor A C} {X : C}

/-- The source map of an identity strict costructured-arrow morphism is an identity. -/
@[simp]
theorem id_map (S : StrictCostructuredArrow K X) :
    map (𝟙 S) = 𝟙 S.left := sorry

/-- The source map of a composite strict costructured-arrow morphism is the composite source map. -/
@[simp]
theorem comp_map {S T U : StrictCostructuredArrow K X} (f : S ⟶ T) (g : T ⟶ U) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Equality transport between strict costructured-arrow objects maps to equality transport between
their source objects. -/
@[simp]
theorem eqToHom_map {S T : StrictCostructuredArrow K X} (h : S = T) :
    map (eqToHom h : S ⟶ T) = eqToHom (congrArg StrictCostructuredArrow.left h) := sorry

/-- The source cell of an identity `2`-morphism is an identity cell. -/
@[simp]
theorem id_map₂ {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    map₂ (𝟙 f) = 𝟙 (map f) := sorry

/-- The source cell of a vertical composite is the vertical composite of the source cells. -/
@[simp]
theorem comp_map₂ {S T : StrictCostructuredArrow K X} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := sorry

/-- Equality transport between strict costructured-arrow morphisms maps to equality transport
between their source maps. -/
@[simp]
theorem eqToHom_map₂ {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (h : f = g) :
    map₂ (eqToHom h : f ⟶ g) = eqToHom (congrArg StrictCostructuredArrow.map h) := sorry

/-- Source cells commute with left whiskering. -/
@[simp]
theorem whiskerLeft_map₂ {S T U : StrictCostructuredArrow K X}
    (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h) :
    map₂ (f ◁ η) = map f ◁ map₂ η := sorry

/-- Source cells commute with right whiskering. -/
@[simp]
theorem whiskerRight_map₂ {S T U : StrictCostructuredArrow K X}
    {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U) :
    map₂ (η ▷ h) = map₂ η ▷ map h := sorry

end StrictCostructuredArrow

end Bicategory

end CategoryTheory
