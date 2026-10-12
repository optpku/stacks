/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Comparison
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Denominator.Final

/-!
# Finality for comma functors induced by localizer morphisms

Denominator refinement is separated from the hypotheses that make it a finality criterion.
For a fully faithful underlying functor, a target-refinement condition and a left calculus in the
target imply finality on target denominators; the source/right-calculus statement is dual.  The
canonical denominator-comma comparisons then transfer these results to localization comma
categories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- Every target denominator in the codomain can be refined by the image of a target
denominator in the domain.  Full faithfulness and a target left calculus are deliberately not
part of this condition; they are the separate hypotheses that turn it into finality. -/
@[stacks 05T5 "target refinements for a localizer morphism"]
class HasTargetRefinements (Φ : LocalizerMorphism W₁ W₂) : Prop where
  /-- A target denominator admits a morphism to one in the image. -/
  exists_refinement : ∀ (X : C₁)
    (U : MorphismProperty.Under W₂ ⊤ (Φ.functor.obj X)),
    ∃ V : MorphismProperty.Under W₁ ⊤ X,
      Nonempty (U ⟶ (Φ.targetDenominators X).obj V)

/-- Every source denominator in the codomain is refined by the image of a source denominator in
the domain.  Full faithfulness and a target right calculus are separate finality hypotheses. -/
@[stacks 05T5 "source refinements for a localizer morphism"]
class HasSourceRefinements (Φ : LocalizerMorphism W₁ W₂) : Prop where
  /-- A source denominator admits a morphism from one in the image. -/
  exists_refinement : ∀ (X : C₁)
    (U : MorphismProperty.Over W₂ ⊤ (Φ.functor.obj X)),
    ∃ V : MorphismProperty.Over W₁ ⊤ X,
      Nonempty ((Φ.sourceDenominators X).obj V ⟶ U)

namespace targetDenominators

/-- Faithfulness of a localizer morphism descends to each target-denominator functor. -/
instance faithful (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Faithful] (X : C₁) :
    (Φ.targetDenominators X).Faithful := sorry

/-- Full faithfulness of the underlying localizer functor makes each target-denominator functor
full. -/
instance full (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Full] [Φ.functor.Faithful]
    (X : C₁) :
    (Φ.targetDenominators X).Full := sorry

/-- Target refinements are a finality criterion for a fully faithful localizer morphism when the
target system has a left calculus of fractions. -/
instance final (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Full] [Φ.functor.Faithful]
    [W₂.HasLeftCalculusOfFractions] [Φ.HasTargetRefinements] (X : C₁) :
    Functor.Final (Φ.targetDenominators X) := sorry

end targetDenominators

namespace sourceDenominators

/-- Faithfulness of a localizer morphism descends to each source-denominator functor. -/
instance faithful (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Faithful] (X : C₁) :
    (Φ.sourceDenominators X).Faithful := sorry

/-- Full faithfulness of the underlying localizer functor makes each source-denominator functor
full. -/
instance full (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Full] [Φ.functor.Faithful]
    (X : C₁) :
    (Φ.sourceDenominators X).Full := sorry

/-- Source refinements are an initiality criterion for a fully faithful localizer morphism when
the target system has a right calculus of fractions. -/
instance initial (Φ : LocalizerMorphism W₁ W₂) [Φ.functor.Full] [Φ.functor.Faithful]
    [W₂.HasRightCalculusOfFractions] [Φ.HasSourceRefinements] (X : C₁) :
    Functor.Initial (Φ.sourceDenominators X) := sorry

end sourceDenominators

namespace costructuredArrow

/-- Finality on target denominators transfers to the induced localization
costructured-arrow functor. -/
instance final (Φ : LocalizerMorphism W₁ W₂)
    [W₁.HasLeftCalculusOfFractions] [W₂.HasLeftCalculusOfFractions]
    (X : C₁) [Functor.Final (Φ.targetDenominators X)] :
    Functor.Final (Φ.costructuredArrow X) := sorry

end costructuredArrow

namespace structuredArrow

/-- Initiality on source denominators transfers to the induced localization structured-arrow
functor. -/
instance initial (Φ : LocalizerMorphism W₁ W₂)
    [W₁.HasRightCalculusOfFractions] [W₂.HasRightCalculusOfFractions]
    (X : C₁) [Functor.Initial (Φ.sourceDenominators X)] :
    Functor.Initial (Φ.structuredArrow X) := sorry

end structuredArrow

#synth (LocalizerMorphism.id W₁).functor.Faithful

end CategoryTheory.LocalizerMorphism
