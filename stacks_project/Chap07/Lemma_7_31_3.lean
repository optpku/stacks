module

public import ReasLib.CategoryTheory.Adjunction.LeftExact.Localization
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.31.3

Localized inverse-image pullback and base-change are category-theoretic
properties of a left-exact adjunction. They are owned by ReasLib and recalled
here in their source-facing specialization to a morphism of topoi.
-/

@[expose] public section

/- Lemma 7.31.3 (04IV): localized inverse image sends a slice object to the
expected pullback object and commutes with further slice pullback in a
commutative localization square. -/
@[stacks 04IV "object"] #check @CategoryTheory.LeftExactAdjunction.Localization.inverseImagePullback_obj

@[stacks 04IV "pullback comparison"] #check @CategoryTheory.LeftExactAdjunction.Localization.inverseImagePullbackIso

@[stacks 04IV "base change"] #check @CategoryTheory.LeftExactAdjunction.Localization.inverseImageBaseChangeIso
