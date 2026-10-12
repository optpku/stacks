/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.PureExt
public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution.HomComplex
import stacks_project.Chap46.Definition_46_8_8_PureInjectiveResolution
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 46.8.9 (1): positive-degree pure extension modules vanish when the target module is
pure injective. -/
@[stacks 0706] #check
  (ModuleCat.PureInjectiveCoresolution.pureExt_isZero_of_pureInjective :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A},
      (I : ModuleCat.PureInjectiveCoresolution N) → N.PureInjective → (i : ℕ) → 0 < i →
        IsZero (I.pureExt M i))

/- Lemma 46.8.9 (2): positive-degree pure extension modules vanish when the source module is
pure projective. -/
@[stacks 0706] #check
  (ModuleCat.PureInjectiveCoresolution.pureExt_isZero_of_pureProjective :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A},
      (I : ModuleCat.PureInjectiveCoresolution N) → M.PureProjective → (i : ℕ) → 0 < i →
        IsZero (I.pureExt M i))

/- Lemma 46.8.9 (3): in particular, positive-degree pure extension modules vanish when the
source module is finitely presented. -/
@[stacks 0706] #check
  (ModuleCat.PureInjectiveCoresolution.pureExt_isZero_of_finitePresentation :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A},
      (I : ModuleCat.PureInjectiveCoresolution N) → [Module.FinitePresentation A M] →
        (i : ℕ) → 0 < i →
          IsZero (I.pureExt M i))

/- Lemma 46.8.9 (4): a pure projective resolution computes the pure extension module as the
corresponding cohomology module of its Hom complex. -/
@[stacks 0706] #check
  (ModuleCat.PureInjectiveCoresolution.pureExt_isIsomorphic_homology :
    ∀ {A : Type u} [CommRing A] {M N : ModuleCat.{v} A},
      (I : ModuleCat.PureInjectiveCoresolution N) →
        (P : ModuleCat.PureProjectiveResolution M) →
        (i : ℕ) →
          IsIsomorphic (I.pureExt M i) ((P.homComplex N).homology (i : ℤ)))
