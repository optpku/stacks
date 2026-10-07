module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap73.Lemma_73_7_8_Topology

/-!
# Fppf hypercoverings of algebraic spaces

An augmentation `a : U ⟶ X` of a simplicial algebraic space is an fppf hypercovering
when the degree-zero map, the degree-one matching map, and all higher relative matching
maps are flat, locally of finite presentation, and surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

/-- The morphism property of being flat, locally of finite presentation, and surjective. -/
abbrev fppfArrows (S : Scheme.{u}) : MorphismProperty (AlgebraicSpace S) :=
  @Flat S ⊓ @LocallyOfFinitePresentation S ⊓ @Surjective S

/-- A morphism of algebraic spaces lies in `fppfArrows` iff it is flat, locally of finite
presentation, and surjective. -/
theorem fppfArrows_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    fppfArrows S f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f :=
  sorry

/-- An augmentation `a : U ⟶ X` is an fppf hypercovering when its degree-zero map and
every relative matching map are flat, locally of finite presentation, and surjective. -/
abbrev IsFppfHypercovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) : Prop :=
  MorphismProperty.Hypercovering (fppfArrows S)
    (SimplicialObject.Augmentation.toAugmented a).toOver

/-- `IsFppfHypercovering` is the morphism-property hypercovering condition for `fppfArrows`. -/
theorem isFppfHypercovering_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    IsFppfHypercovering a =
      MorphismProperty.Hypercovering (fppfArrows S)
        (SimplicialObject.Augmentation.toAugmented a).toOver :=
  sorry

/-- An fppf hypercovering is equivalently the three source matching conditions: `U.obj (op ⦋0⦌) ⟶ X`,
`U.obj (op ⦋1⦌) ⟶ pullback` of the two copies of the degree-zero map, and
`U.obj (op ⦋n + 2⦌) ⟶ ((cosk (n + 1)).obj (toOver a)).obj (op ⦋n + 2⦌)` for all `n`. -/
theorem isFppfHypercovering_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    IsFppfHypercovering a ↔
      fppfArrows S (SimplicialObject.Augmented.zeroMap
          (SimplicialObject.Augmentation.toAugmented a)) ∧
        fppfArrows S (SimplicialObject.Augmented.oneMap
          (SimplicialObject.Augmentation.toAugmented a)) ∧
        ∀ n : ℕ,
          fppfArrows S (SimplicialObject.Augmented.relativeMatchingMap
            (SimplicialObject.Augmentation.toAugmented a) (n + 1)) :=
  sorry

/-- The degree-zero map of an fppf hypercovering is flat, locally of finite presentation,
and surjective. -/
theorem isFppfHypercovering_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a) :
    fppfArrows S (SimplicialObject.Augmented.zeroMap
      (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- The degree-one matching map of an fppf hypercovering is flat, locally of finite
presentation, and surjective. -/
theorem isFppfHypercovering_one {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a) :
    fppfArrows S (SimplicialObject.Augmented.oneMap
      (SimplicialObject.Augmentation.toAugmented a)) :=
  sorry

/-- Every successor-level relative matching map of an fppf hypercovering is flat, locally of
finite presentation, and surjective. -/
theorem isFppfHypercovering_higher {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a) (n : ℕ) :
    fppfArrows S (SimplicialObject.Augmented.relativeMatchingMap
      (SimplicialObject.Augmentation.toAugmented a) (n + 1)) :=
  sorry

/-- An fppf hypercovering is a hypercovering for the fppf topology on algebraic spaces
over `S`. The converse fails: `fppfTopology.coveringArrows` only asks that the generated
singleton sieve is covering, so it properly contains `fppfArrows`. -/
theorem isHypercovering_of_isFppfHypercovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a) :
    (SimplicialObject.Augmentation.toAugmented a).IsHypercovering (fppfTopology S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
