/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.KoszulLimit.Reflector
import StacksCheckRecall

/-!
# Powered-Koszul derived completion is a reflector

The reusable owner constructs the adjunction and reflector from a functor whose unit components
are the canonical comparisons with powered-Koszul derived limits.

@stack 0920
-/

@[expose] public section

/- Lemma 15.92.18 (0920): in Situation 15.92.15, the functor
`K ↦ Rlim (K ⊗ᴸ_A K_n^•)` is left adjoint to the inclusion of the full subcategory of objects
derived complete with respect to `Ideal.span (Set.range f)`. -/
@[stacks 0920 "Lemma 15.92.18"]
#check @CategoryTheory.DerivedCategory.KoszulLimit.Reflector.adjunction

/- The hypothesis records that every unit component is the canonical comparison with the
corresponding powered-Koszul derived limit. -/
#check @CategoryTheory.DerivedCategory.KoszulLimit.Reflector.ComparisonUnit

/- The owner retains the comparison isomorphism and explicit counit data used by the adjunction. -/
#check @CategoryTheory.DerivedCategory.KoszulLimit.Reflector.unitAppIso
#check @CategoryTheory.DerivedCategory.KoszulLimit.Reflector.counit

/- The same data is packaged as a reflector, so it can be compared canonically with the selected
derived-completion reflector of Lemma 15.92.10. -/
#check @CategoryTheory.DerivedCategory.KoszulLimit.Reflector.reflector
#check @DerivedCategory.DerivedCompletion.chosenReflectorIso
