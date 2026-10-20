/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Automorphism-group properties at a point

A property `P` of algebraic spaces over fields that is invariant under ground
field extensions descends from field-valued representatives to a well-defined
property of a point `x ∈ |X|` of an algebraic stack. Finite, smooth, and
proper automorphism groups at a point are the standing examples.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.smooth_isInvariantUnderGroundFieldExtension :
  ∀ {S : Scheme.{u}},
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Smooth S))

#check (AlgebraicGeometry.AlgebraicStack.proper_isInvariantUnderGroundFieldExtension :
  ∀ {S : Scheme.{u}},
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.Proper S))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt_iff_exists :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] (x : Points X),
    automorphismGroup.HasAt P x ↔
      ∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.Has P p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt.spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : Points X},
    automorphismGroup.HasAt P x →
      ∀ p : FieldValuedPoint X, Points.mk p = x → automorphismGroup.Has P p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.HasAt.of_fieldValuedPoint :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] {x : Points X} {p : FieldValuedPoint X},
    Points.mk p = x → automorphismGroup.Has P p → automorphismGroup.HasAt P x)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsFinite :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsFinite_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X),
    automorphismGroup.IsFinite x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has (@AlgebraicSpace.IsFinite S) p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Smooth :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Smooth_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X),
    automorphismGroup.Smooth x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has (@AlgebraicSpace.Smooth S) p)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Proper :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Proper_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X),
    automorphismGroup.Proper x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has (@AlgebraicSpace.Proper S) p)

end AlgebraicGeometry.AlgebraicStack
