/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-! # Fppf hypercoverings of algebraic spaces -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Functor
open scoped Simplicial

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

#check (fppfArrows : ∀ (S : Scheme.{u}), MorphismProperty (AlgebraicSpace S))

#check (fppfArrows_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    fppfArrows S f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f)

#check (IsFppfHypercovering : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X), Prop)

#check (isFppfHypercovering_eq : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X), IsFppfHypercovering a =
      MorphismProperty.Hypercovering (fppfArrows S)
        (SimplicialObject.Augmentation.toAugmented a).toOver)

#check (isFppfHypercovering_iff : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X),
    IsFppfHypercovering a ↔
      fppfArrows S (SimplicialObject.Augmented.zeroMap
          (SimplicialObject.Augmentation.toAugmented a)) ∧
        fppfArrows S (SimplicialObject.Augmented.oneMap
          (SimplicialObject.Augmentation.toAugmented a)) ∧
        ∀ n : ℕ,
          fppfArrows S ((SimplicialObject.matchingMap
            (SimplicialObject.Augmentation.toAugmented a).toOver (n + 1)).left))

#check (isFppfHypercovering_zero : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a),
    fppfArrows S (SimplicialObject.Augmented.zeroMap
      (SimplicialObject.Augmentation.toAugmented a)))

#check (isFppfHypercovering_one : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a),
    fppfArrows S (SimplicialObject.Augmented.oneMap
      (SimplicialObject.Augmentation.toAugmented a)))

#check (isFppfHypercovering_higher : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    {a : U ⟶ (const SimplexCategoryᵒᵖ).obj X} (ha : IsFppfHypercovering a) (n : ℕ),
    fppfArrows S ((SimplicialObject.matchingMap
      (SimplicialObject.Augmentation.toAugmented a).toOver (n + 1)).left))

end AlgebraicGeometry.AlgebraicSpace.Simplicial
