/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective amplitude from derived extension groups

@stack 0A5T

The forward vanishing statement only uses a bounded injective representative.  Reconstructing
such a representative from one boundary group uses enough injectives, while detecting both
t-structure bounds from all heart objects also uses enough projectives.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A bounded injective representative makes every derived extension group from a heart object
outside its support interval subsingleton. -/
@[stacks 0A5T "forward vanishing"]
theorem HasInjectiveAmplitudeIn.ext_subsingleton
    {K : DerivedCategory C} {a b i : ℤ} (hK : HasInjectiveAmplitudeIn K a b)
    (N : C) (hi : i ∉ Set.Icc a b) :
    Subsingleton (Ext⁽i⁾((DerivedCategory.singleFunctor C 0).obj N, K)) := sorry

/-- Elementwise form of `HasInjectiveAmplitudeIn.ext_subsingleton`. -/
theorem HasInjectiveAmplitudeIn.ext_eq_zero
    {K : DerivedCategory C} {a b i : ℤ} (hK : HasInjectiveAmplitudeIn K a b)
    (N : C) (hi : i ∉ Set.Icc a b)
    (e : Ext⁽i⁾((DerivedCategory.singleFunctor C 0).obj N, K)) :
    e = 0 := sorry

namespace InjectiveAmplitude

variable [EnoughInjectives C]

/-- T-structure bounds together with vanishing in the first degree above the upper bound produce
a representative by injectives supported in the prescribed interval. -/
@[stacks 0A5T "boundary reconstruction"]
theorem of_isGE_isLE_ext_succ
    {K : DerivedCategory C} {a b : ℤ} (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hExt : ∀ N : C,
      Subsingleton (Ext⁽b + 1⁾((DerivedCategory.singleFunctor C 0).obj N, K))) :
    HasInjectiveAmplitudeIn K a b := sorry

/-- Injective amplitude is equivalent to its two t-structure bounds and vanishing of the first
extension group above the upper endpoint. -/
@[stacks 0A5T "bounded abstract form"]
theorem iff_isGE_isLE_ext_succ (K : DerivedCategory C) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      K.IsGE a ∧ K.IsLE b ∧
        ∀ N : C,
          Subsingleton (Ext⁽b + 1⁾((DerivedCategory.singleFunctor C 0).obj N, K)) := sorry

/-- Lemma 15.70.2, abstract heart-object form: in an abelian category with enough projectives and
injectives, injective amplitude in `[a, b]` is detected by vanishing of all derived extensions
from heart objects outside that interval. -/
@[stacks 0A5T "abstract heart-object form"]
theorem iff_ext_subsingleton [EnoughProjectives C]
    (K : DerivedCategory C) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∀ (N : C) (i : ℤ), i ∉ Set.Icc a b →
        Subsingleton (Ext⁽i⁾((DerivedCategory.singleFunctor C 0).obj N, K)) := sorry

end InjectiveAmplitude

end CategoryTheory.DerivedCategory
