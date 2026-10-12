/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Map
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hypercoverings for morphism properties

This leaf provides the relative simplicial hypercovering condition associated to an arbitrary
morphism property.  It is independent of any chosen Grothendieck topology: the simplicial object
lives in a slice category and its matching maps are expressed using relative coskeleta.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open Limits Opposite
open scoped Simplicial

universe v u

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- A relative simplicial hypercovering whose degree-zero arrow and every
matching map belong to a prescribed morphism property. -/
@[stacks 0DER]
structure Hypercovering (P : MorphismProperty C) {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) : Prop where
  /-- The degree-zero augmentation belongs to `P`. -/
  zero_mem : P ((U.obj (Opposite.op ⦋0⦌)).hom)
  /-- Every relative matching map belongs to `P`. -/
  matching_mem (n : ℕ) : P ((SimplicialObject.matchingMap U n).left)

namespace Hypercovering

/-- A degree-zero augmentation and relative matching maps in `P` define a hypercovering. -/
def ofConditions {P : MorphismProperty C} {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)}
    (h_zero : P ((U.obj (Opposite.op ⦋0⦌)).hom))
    (h_matching : ∀ n : ℕ, P ((SimplicialObject.matchingMap U n).left)) :
    Hypercovering P U where
  zero_mem := h_zero
  matching_mem := h_matching

/-- A relative simplicial object is a hypercovering for `P` exactly when its degree-zero
augmentation and all relative matching maps belong to `P`. -/
theorem iff_zero_matching {P : MorphismProperty C} {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) :
    Hypercovering P U ↔
      P ((U.obj (Opposite.op ⦋0⦌)).hom) ∧
        ∀ n : ℕ, P ((SimplicialObject.matchingMap U n).left) := sorry

/-- The degree-one relative matching map belongs to `P`. -/
theorem one_mem {P : MorphismProperty C} {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U) :
    P ((SimplicialObject.matchingMap U 0).left) := sorry

/-- Every successor-level relative matching map belongs to `P`. -/
theorem higher_mem {P : MorphismProperty C} {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U) (n : ℕ) :
    P ((SimplicialObject.matchingMap U (n + 1)).left) := sorry

/-- The degree-zero, degree-one, and successor-level matching conditions construct a relative
hypercovering. -/
theorem of_zero_one_higher {P : MorphismProperty C} {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)}
    (h_zero : P ((U.obj (Opposite.op ⦋0⦌)).hom))
    (h_one : P ((SimplicialObject.matchingMap U 0).left))
    (h_higher : ∀ n : ℕ, P ((SimplicialObject.matchingMap U (n + 1)).left)) :
    Hypercovering P U := sorry

/-- Every augmentation of a relative hypercovering belongs to `P` when `P`
is stable under base change and multiplicative. -/
@[stacks 0DER]
theorem augmentation_mem
    {P : MorphismProperty C} [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U) (n : ℕ) :
    P ((U.obj (Opposite.op ⦋n⦌)).hom) := sorry

/-- The source-facing augmentation criterion with an explicit hypothesis that `P` contains all
isomorphisms. -/
theorem augmentation_mem_of_isomorphisms
    {P : MorphismProperty C} [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hP_iso : ∀ {Y Z : C} (f : Y ⟶ Z), IsIso f → P f)
    {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U) (n : ℕ) :
    P ((U.obj (Opposite.op ⦋n⦌)).hom) := sorry

/-- Every face map of a relative hypercovering belongs to `P` when `P` is
stable under base change and multiplicative. -/
@[stacks 0DER]
theorem faceMap_mem
    {P : MorphismProperty C} [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U)
    (n : ℕ) (i : Fin (n + 2)) :
    P ((U.δ i).left) := sorry

/-- The source-facing face-map criterion with an explicit hypothesis that `P` contains all
isomorphisms. -/
theorem faceMap_mem_of_isomorphisms
    {P : MorphismProperty C} [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hP_iso : ∀ {Y Z : C} (f : Y ⟶ Z), IsIso f → P f)
    {X : C} [HasPullbacks C]
    {U : SimplicialObject (Over X)} (hU : Hypercovering P U)
    (n : ℕ) (i : Fin (n + 2)) :
    P ((U.δ i).left) := sorry

end Hypercovering

end MorphismProperty

end CategoryTheory
