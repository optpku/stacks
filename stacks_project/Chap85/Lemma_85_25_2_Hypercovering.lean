/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.Topology.Category.LCCat.Covering

/-!
# Proper hypercoverings in `LCCat`

An augmentation `a : U ⟶ X` of a simplicial object of `LCCat` is a proper
hypercovering when the degree-zero map, the degree-one matching map, and all
higher relative matching maps are proper and surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

noncomputable section

namespace LCCat

/-- Surjective morphisms in `LCCat`. -/
abbrev surjective : MorphismProperty LCCat.{u} :=
  fun _ _ f ↦ Function.Surjective f.hom

/-- Proper surjective morphisms in `LCCat`. -/
abbrev properSurjective : MorphismProperty LCCat.{u} :=
  proper ⊓ surjective

/-- An augmentation `a : U ⟶ X` is a proper hypercovering when its degree-zero map and
every relative matching map are proper and surjective. -/
abbrev IsProperHypercovering {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) : Prop :=
  MorphismProperty.Hypercovering properSurjective
    (SimplicialObject.Augmentation.toAugmented a).toOver

/-- `IsProperHypercovering` is the morphism-property hypercovering condition for
`properSurjective`. -/
theorem isProperHypercovering_eq {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) :
    IsProperHypercovering a =
      MorphismProperty.Hypercovering properSurjective
        (SimplicialObject.Augmentation.toAugmented a).toOver :=
  sorry

/-- A proper hypercovering is equivalently the three source matching conditions:
`U.obj (op ⦋0⦌) ⟶ X`, `U.obj (op ⦋1⦌) ⟶ pullback` of the two copies of the
degree-zero map, and the relative matching maps of `toAugmented a` in degrees
`n + 1` for all `n`. -/
theorem isProperHypercovering_iff {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) :
    IsProperHypercovering a ↔
      properSurjective
          (SimplicialObject.Augmented.zeroMap
            (SimplicialObject.Augmentation.toAugmented a)) ∧
        properSurjective
          (SimplicialObject.Augmented.oneMap
            (SimplicialObject.Augmentation.toAugmented a)) ∧
        ∀ n : ℕ,
          properSurjective
            (SimplicialObject.Augmented.relativeMatchingMap
              (SimplicialObject.Augmentation.toAugmented a) (n + 1)) :=
  sorry

/-- The degree-zero map of a proper hypercovering is proper and surjective. -/
theorem isProperHypercovering_zero {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    {a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X} (ha : IsProperHypercovering a) :
    properSurjective
      (SimplicialObject.Augmented.zeroMap
        (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- The degree-one matching map of a proper hypercovering is proper and surjective. -/
theorem isProperHypercovering_one {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    {a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X} (ha : IsProperHypercovering a) :
    properSurjective
      (SimplicialObject.Augmented.oneMap
        (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- Every successor-level relative matching map of a proper hypercovering is proper and
surjective. -/
theorem isProperHypercovering_higher {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    {a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X} (ha : IsProperHypercovering a) (n : ℕ) :
    properSurjective
      (SimplicialObject.Augmented.relativeMatchingMap
        (SimplicialObject.Augmentation.toAugmented a) (n + 1)) :=
  sorry

/-- The degree-zero, degree-one, and higher matching conditions construct a proper
hypercovering. -/
theorem isProperHypercovering_of_zero_one_higher {U : SimplicialObject LCCat.{u}}
    {X : LCCat.{u}} (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
    (h_zero : properSurjective
      (SimplicialObject.Augmented.zeroMap
        (SimplicialObject.Augmentation.toAugmented a)))
    (h_one : properSurjective
      (SimplicialObject.Augmented.oneMap
        (SimplicialObject.Augmentation.toAugmented a)))
    (h_higher : ∀ n : ℕ, properSurjective
      (SimplicialObject.Augmented.relativeMatchingMap
        (SimplicialObject.Augmentation.toAugmented a) (n + 1))) :
    IsProperHypercovering a :=
  sorry

end LCCat

end
