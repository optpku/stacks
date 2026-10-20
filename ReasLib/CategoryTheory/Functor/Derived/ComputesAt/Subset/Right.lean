module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Right Derived Functors from a Good Subset

This leaf turns a denominator-cofinal object property on which a functor inverts the relevant
denominators into right-derived computation and source-definedness everywhere. The primary
conclusions retain essential constancy; the weaker Mathlib pointwise-existence consequence remains
available separately. Everything is stated for an arbitrary saturated multiplicative system,
independently of any derived-category presentation.  The full-subcategory API uses mathlib's
canonical right-resolution interface, so applications do not unpack denominator witnesses.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open MorphismProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.IsSaturatedMultiplicativeSystem]

/-- Stacks 06XN: an object in a denominator-cofinal good subset computes the pointwise
right-derived value when `F` inverts denominators between good objects. -/
@[stacks 06XN]
theorem RightDerived.ComputesAt.of_mem_subset
    (I : ObjectProperty D)
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))
    {X : D} (hX : I X) :
    RightDerived.ComputesAt F S X := sorry

/-- Stacks 06XN: a denominator-cofinal object property on which the functor inverts internal
denominators makes the right-derived functor source-defined everywhere. -/
@[stacks 06XN]
theorem RightDerived.EverywhereDefined.of_subset
    (I : ObjectProperty D)
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    Functor.RightDerived.EverywhereDefined F S := sorry

/-- Stacks 06XN: a denominator-cofinal object property on which `F` inverts denominators
supplies pointwise right-derived values at every object. -/
@[stacks 06XN]
theorem RightDerived.EverywhereDefined.hasPointwise_of_subset
    (I : ObjectProperty D)
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    F.HasPointwiseRightDerivedFunctor S := sorry

/-- Stacks 09LI: a denominator-cofinal object property on which `F` inverts internal
denominators supplies a total right-derived functor. This is an ordinary theorem rather than a
proof-dependent instance, so callers install it only at a concrete derived construction. -/
@[stacks 09LI]
theorem RightDerived.EverywhereDefined.hasFunctor_of_subset
    (I : ObjectProperty D)
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    F.HasRightDerivedFunctor S := sorry

/-- Stacks 06XN: an object in a full subcategory admitting right resolutions computes its
right-derived value when the restricted denominator system is inverted by `P.ι ⋙ F`. -/
@[stacks 06XN "right-derived computation from a full subcategory"]
theorem RightDerived.ComputesAt.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F))
    {X : D} (hX : P X) :
    RightDerived.ComputesAt F S X := sorry

/-- Stacks 06XN: right resolutions by a full subcategory on which `P.ι ⋙ F` inverts the
restricted denominators make the right-derived functor source-defined everywhere. -/
@[stacks 06XN "right-derived source-definedness from a full subcategory"]
theorem RightDerived.EverywhereDefined.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    Functor.RightDerived.EverywhereDefined F S := sorry

/-- Stacks 06XN: right resolutions by a full subcategory on which the restricted functor
inverts denominators supply pointwise right-derived values at every object. -/
@[stacks 06XN "pointwise right-derived existence from a full subcategory"]
theorem RightDerived.EverywhereDefined.hasPointwise_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasPointwiseRightDerivedFunctor S := sorry

/-- Stacks 09LI: right resolutions by a full subcategory on which the restricted functor
inverts denominators supply a total right-derived functor. -/
@[stacks 06XN "total right-derived functor from a full subcategory",
  stacks 09LI "total right-derived functor from right resolutions"]
theorem RightDerived.EverywhereDefined.hasFunctor_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasRightDerivedFunctor S := sorry


end CategoryTheory.Functor
