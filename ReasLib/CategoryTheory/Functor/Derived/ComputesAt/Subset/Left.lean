/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left Derived Functors from a Good Subset

This leaf is the left-derived dual of the corresponding right-subset criterion. A
denominator-cofinal object property on which a functor inverts the relevant denominators supplies
left-derived computation and source-definedness everywhere without choosing a particular
derived-category model. The weaker Mathlib pointwise-existence consequence remains available
separately.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open MorphismProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.IsSaturatedMultiplicativeSystem]

/-- Stacks 06XN: an object in a denominator-cofinal good subset computes the pointwise
left-derived value when `F` inverts denominators between good objects. -/
@[stacks 06XN, stacks 0FTF "good objects compute a left-derived functor"]
theorem LeftDerived.ComputesAt.of_mem_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    {X : D} (hX : P X) :
    LeftDerived.ComputesAt F S X := sorry

/-- Stacks 06XN: a denominator-cofinal object property on which the functor inverts internal
denominators makes the left-derived functor source-defined everywhere. -/
@[stacks 06XN, stacks 0FTF "cofinal good objects define a left-derived functor"]
theorem LeftDerived.EverywhereDefined.of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    Functor.LeftDerived.EverywhereDefined F S := sorry

/-- Stacks 06XN: a denominator-cofinal object property on which `F` inverts denominators
supplies pointwise left-derived values at every object. -/
@[stacks 06XN]
theorem LeftDerived.EverywhereDefined.hasPointwise_of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor S := sorry

/-- Stacks 06XN: a denominator-cofinal object property on which `F` inverts internal
denominators supplies a total left-derived functor. This is an ordinary theorem rather than a
proof-dependent instance, so a caller can install the result only where a concrete derived
construction needs it. -/
@[stacks 06XN]
theorem LeftDerived.EverywhereDefined.hasFunctor_of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    F.HasLeftDerivedFunctor S := sorry

/-- Stacks 06XN: an object in a full subcategory admitting left resolutions computes its
left-derived value when the restricted denominator system is inverted by `P.ι ⋙ F`. -/
@[stacks 06XN "left-derived computation from a full subcategory"]
theorem LeftDerived.ComputesAt.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F))
    {X : D} (hX : P X) :
    LeftDerived.ComputesAt F S X := sorry

/-- Stacks 06XN: left resolutions by a full subcategory on which `P.ι ⋙ F` inverts the
restricted denominators make the left-derived functor source-defined everywhere. -/
@[stacks 06XN "left-derived source-definedness from a full subcategory"]
theorem LeftDerived.EverywhereDefined.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    Functor.LeftDerived.EverywhereDefined F S := sorry

/-- Stacks 06XN: left resolutions by a full subcategory on which the restricted functor
inverts denominators supply pointwise left-derived values at every object. -/
@[stacks 06XN "pointwise left-derived existence from a full subcategory"]
theorem LeftDerived.EverywhereDefined.hasPointwise_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasPointwiseLeftDerivedFunctor S := sorry

/-- Stacks 06XN: left resolutions by a full subcategory on which the restricted functor
inverts denominators supply a total left-derived functor. -/
@[stacks 06XN "total left-derived functor from a full subcategory"]
theorem LeftDerived.EverywhereDefined.hasFunctor_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasLeftDerivedFunctor S := sorry


end CategoryTheory.Functor
