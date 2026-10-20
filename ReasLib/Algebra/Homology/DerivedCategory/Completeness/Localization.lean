module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completion and principal localization

An object on which an element of a finitely generated ideal acts invertibly has zero derived
completion.  The essential-image specialization records the equivalent localization-away model
without making that model the source-facing hypothesis.

@stack 0A6D
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DerivedCategory.DerivedCompletion

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.12: if some `f ∈ I` acts invertibly on a derived `A`-module `K`, then the
derived completion of `K` with respect to the finitely generated ideal `I` is zero. -/
@[stacks 0A6D "derived completion vanishes after inverting an ideal element"]
theorem isZero_of_isIso_smul (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I)
    (K : DerivedCategory (ModuleCat A)) [IsIso (f • 𝟙 K)] :
    IsZero (derivedCompletionOf I hI K) := sorry

/-- The localization-away essential-image form of `isZero_of_isIso_smul`: an object obtained by
derived restriction from `A_f` has zero derived completion whenever `f ∈ I`. -/
@[stacks 0A6D "localization-away form of derived-completion vanishing"]
theorem isZero_of_mem_localizationAway_essImage
    (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I)
    {K : DerivedCategory (ModuleCat A)}
    (hK : (CategoryTheory.ModuleCat.derivedRestrictionOfScalars
      (algebraMap A (Localization.Away f))).essImage K) :
    IsZero (derivedCompletionOf I hI K) := sorry

end DerivedCategory.DerivedCompletion
