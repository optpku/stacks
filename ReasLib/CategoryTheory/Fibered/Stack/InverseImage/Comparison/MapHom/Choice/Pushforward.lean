/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.Direct

/-!
# Pushforward-choice independence of direct inverse image

This leaf changes the proof that pushforward inverts the relevant fractions while keeping the
stackification quasi-inverse fixed. Since the inversion family is proposition-valued, the
comparison has identity components and requires no equality transport.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.mapHom

variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

/-- Direct inverse-image morphism functors are canonically independent of the proof supplying
pushforward inversion, with the stackification quasi-inverse held fixed. -/
@[stacks 04WS "pushforward-choice independence for inverse-image morphisms"]
noncomputable def inversionChoiceIso
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    mapHom I I' h q ≅ mapHom I I' h' q :=
  Functor.isoWhiskerRight (StackOver.Pushforward.mapFunctor.choiceIso u h h')
    (StackOver.Hom.PrecompLift.mapFunctor I'.comparisonHom q)

/-- The forward component of inverse-image pushforward-choice independence is the identity. -/
@[simp, stacks 04WS "pushforward-choice inverse-image forward component"]
theorem inversionChoiceIso.hom.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (inversionChoiceIso I I' h h' q).hom.app F =
      𝟙 ((mapHom I I' h q).obj F) := sorry

/-- The inverse component of inverse-image pushforward-choice independence is the identity. -/
@[simp, stacks 04WS "pushforward-choice inverse-image inverse component"]
theorem inversionChoiceIso.inv.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (F : S ⟶ S') :
    (inversionChoiceIso I I' h h' q).inv.app F =
      𝟙 ((mapHom I I' h' q).obj F) := sorry

/-- Changing the pushforward inversion proof preserves the stackification comparison. -/
@[stacks 04WS "pushforward-choice inverse-image comparison coherence"]
theorem inversionChoiceIso.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    Functor.isoWhiskerRight (inversionChoiceIso I I' h h' q)
          (StackOver.Hom.precomp I'.target I.comparisonHom) ≪≫
        comparisonIso I I' h' q =
      comparisonIso I I' h q ≪≫
        Functor.isoWhiskerRight (StackOver.Pushforward.mapFunctor.choiceIso u h h')
          (Bicategory.postcomp
            (FiberedCategoryOver.pushforward u S.toFiberedCategoryOver h.source)
            I'.comparisonHom) := sorry

/-- Comparing a pushforward inversion proof with itself gives the identity isomorphism. -/
@[simp, stacks 04WS "pushforward-choice inverse-image reflexivity"]
theorem inversionChoiceIso.refl
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    inversionChoiceIso I I' h h q = Iso.refl (mapHom I I' h q) := sorry

/-- Reversing a pushforward-choice comparison exchanges its inversion proofs. -/
@[simp, stacks 04WS "pushforward-choice inverse-image symmetry"]
theorem inversionChoiceIso.symm
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h h' : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    (inversionChoiceIso I I' h h' q).symm =
      inversionChoiceIso I I' h' h q := sorry

/-- Pushforward inversion-choice comparisons compose transitively. -/
@[stacks 04WS "pushforward-choice inverse-image transitivity"]
theorem inversionChoiceIso.trans
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h₀ h₁ h₂ : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom)) :
    inversionChoiceIso I I' h₀ h₁ q ≪≫ inversionChoiceIso I I' h₁ h₂ q =
      inversionChoiceIso I I' h₀ h₂ q := sorry

/- Axiom audit: the comparison is obtained by whiskering identity choice data for stack
pushforward; no equality-transport morphism is introduced. -/

end StackOver.InverseImage.mapHom

end CategoryTheory
