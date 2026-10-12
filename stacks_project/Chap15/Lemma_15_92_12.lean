/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Localization
import StacksCheckRecall

/-!
# Vanishing of derived completion after localization

@stack 0A6D
-/

@[expose] public section

/- Lemma 15.92.12: if an element `f ∈ I` acts invertibly on `K`, then the derived completion
of `K` with respect to the finitely generated ideal `I` is zero. -/
@[stacks 0A6D "derived completion vanishes after inverting an ideal element"]
#check @DerivedCategory.DerivedCompletion.isZero_of_isIso_smul

/- The equivalent localization-away essential-image formulation used by downstream derived
restriction arguments. -/
#check @DerivedCategory.DerivedCompletion.isZero_of_mem_localizationAway_essImage
