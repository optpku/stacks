module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange

/-!
# Universal and uniform categorical quotients of pre-relations

This module records categorical-quotient stability under arbitrary and flat base change
in a full subcategory of algebraic spaces over a base that is closed under fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- An invariant morphism `φ : U ⟶ X` is a universal categorical quotient in `C` when
the relevant objects lie in `C` and every base change along a morphism in `C` is a
categorical quotient of the base-changed pre-relation. -/
def IsUniversalCategoricalQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} (φ : U ⟶ X) : Prop :=
  C U ∧ C P.left ∧ C X ∧ ∃ hφ : P.IsInvariantHom φ,
    ∀ {X' : Over B} (f : X' ⟶ X), C X' →
      (P.baseChange hφ f).IsCategoricalQuotientIn C (pullback.snd φ f)

/-- A universal categorical quotient is characterized by object membership, invariance, and
categorical-quotient stability after every base change in `C`. -/
theorem isUniversalCategoricalQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} (φ : U ⟶ X) :
    P.IsUniversalCategoricalQuotient C φ ↔
      C U ∧ C P.left ∧ C X ∧ ∃ hφ : P.IsInvariantHom φ,
        ∀ {X' : Over B} (f : X' ⟶ X), C X' →
          (P.baseChange hφ f).IsCategoricalQuotientIn C (pullback.snd φ f) := sorry

/-- A universal categorical quotient has categorical-quotient identity base change. -/
theorem isCategoricalQuotientIn_of_isUniversal {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} {φ : U ⟶ X}
    (h : P.IsUniversalCategoricalQuotient C φ) (hφ : P.IsInvariantHom φ) :
    (P.baseChange hφ (𝟙 X)).IsCategoricalQuotientIn C (pullback.snd φ (𝟙 X)) := sorry

/-- An invariant morphism `φ : U ⟶ X` is a uniform categorical quotient in `C` when
the relevant objects lie in `C` and every flat base change in `C` is a categorical
quotient of the base-changed pre-relation. -/
def IsUniformCategoricalQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} (φ : U ⟶ X) : Prop :=
  C U ∧ C P.left ∧ C X ∧ ∃ hφ : P.IsInvariantHom φ,
    ∀ {X' : Over B} (f : X' ⟶ X), C X' → Flat f.left →
      (P.baseChange hφ f).IsCategoricalQuotientIn C (pullback.snd φ f)

/-- A uniform categorical quotient is characterized by object membership, invariance, and
categorical-quotient stability after every flat base change in `C`. -/
theorem isUniformCategoricalQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} (φ : U ⟶ X) :
    P.IsUniformCategoricalQuotient C φ ↔
      C U ∧ C P.left ∧ C X ∧ ∃ hφ : P.IsInvariantHom φ,
        ∀ {X' : Over B} (f : X' ⟶ X), C X' → Flat f.left →
          (P.baseChange hφ f).IsCategoricalQuotientIn C (pullback.snd φ f) := sorry

/-- A uniform categorical quotient has categorical-quotient identity base change. -/
theorem isCategoricalQuotientIn_of_isUniform {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} {φ : U ⟶ X}
    (h : P.IsUniformCategoricalQuotient C φ) (hφ : P.IsInvariantHom φ) :
    (P.baseChange hφ (𝟙 X)).IsCategoricalQuotientIn C (pullback.snd φ (𝟙 X)) := sorry

/-- Every universal categorical quotient is a uniform categorical quotient. -/
theorem toUniform {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (C : ObjectProperty (Over B))
    [C.IsClosedUnderLimitsOfShape WalkingCospan] {X : Over B} {φ : U ⟶ X}
    (h : P.IsUniversalCategoricalQuotient C φ) :
    P.IsUniformCategoricalQuotient C φ := sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
