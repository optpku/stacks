module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site

/-!
# Proper hypercoverings of algebraic spaces

An augmentation `a : U ⟶ X` of a simplicial algebraic space is a proper hypercovering
when the degree-zero map, the degree-one matching map, and all higher relative matching
maps are proper and surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

/-- An augmentation `a : U ⟶ X` is a proper hypercovering when its degree-zero map and
every relative matching map are proper and surjective. -/
abbrev IsProperHypercovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) : Prop :=
  MorphismProperty.Hypercovering (properSurjectiveMorphismProperty S)
    (SimplicialObject.Augmentation.toAugmented a).toOver

/-- `IsProperHypercovering` is the morphism-property hypercovering condition for
`properSurjectiveMorphismProperty`. -/
theorem isProperHypercovering_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    IsProperHypercovering a =
      MorphismProperty.Hypercovering (properSurjectiveMorphismProperty S)
        (SimplicialObject.Augmentation.toAugmented a).toOver := rfl

/-- A proper hypercovering is equivalently given by the degree-zero, degree-one, and
higher matching conditions: `U.obj (op ⦋0⦌) ⟶ X`, the map from `U.obj (op ⦋1⦌)`
to the fiber product of the two copies of the degree-zero map, and all relative
matching maps in degrees at least two. -/
theorem isProperHypercovering_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    IsProperHypercovering a ↔
      properSurjectiveMorphismProperty S
          (SimplicialObject.Augmented.zeroMap
            (SimplicialObject.Augmentation.toAugmented a)) ∧
        properSurjectiveMorphismProperty S
          (SimplicialObject.Augmented.oneMap
            (SimplicialObject.Augmentation.toAugmented a)) ∧
        ∀ n : ℕ,
          properSurjectiveMorphismProperty S
            ((SimplicialObject.matchingMap
              (SimplicialObject.Augmentation.toAugmented a).toOver (n + 1)).left) :=
  sorry

/-- The degree-zero map of a proper hypercovering is proper and surjective. -/
theorem isProperHypercovering_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsProperHypercovering a) :
    properSurjectiveMorphismProperty S
      (SimplicialObject.Augmented.zeroMap
        (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- The degree-one matching map of a proper hypercovering is proper and surjective. -/
theorem isProperHypercovering_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsProperHypercovering a) :
    properSurjectiveMorphismProperty S
      (SimplicialObject.Augmented.oneMap
        (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- Every successor-level relative matching map of a proper hypercovering is proper and
surjective. -/
theorem isProperHypercovering_higher {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsProperHypercovering a)
    (n : ℕ) :
    properSurjectiveMorphismProperty S
      ((SimplicialObject.matchingMap
        (SimplicialObject.Augmentation.toAugmented a).toOver (n + 1)).left) :=
  sorry

/-- The degree-zero, degree-one, and higher matching conditions construct a proper
hypercovering. -/
theorem isProperHypercovering_of_zero_one_higher {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (h_zero : properSurjectiveMorphismProperty S
      (SimplicialObject.Augmented.zeroMap
        (SimplicialObject.Augmentation.toAugmented a)))
    (h_one : properSurjectiveMorphismProperty S
      (SimplicialObject.Augmented.oneMap
        (SimplicialObject.Augmentation.toAugmented a)))
    (h_higher : ∀ n : ℕ, properSurjectiveMorphismProperty S
      ((SimplicialObject.matchingMap
        (SimplicialObject.Augmentation.toAugmented a).toOver (n + 1)).left)) :
    IsProperHypercovering a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
