/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Ext
import StacksCheckRecall

/-!
# Lemma 15.69.2

@stack 0A5P
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]
variable (K : DerivedCategory (ModuleCat R)) (a b : ℤ)

/- Lemma 15.69.2: projective amplitude in `[a, b]` is equivalent to vanishing of derived Ext
outside `[-b, -a]`, and to the two source cohomology-plus-Ext vanishing formulations. -/
@[stacks 0A5P "projective amplitude and derived Ext vanishing"]
#check
  (projectiveAmplitudeIn_ext_vanishing_tfae K a b :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext⁽i⁾(K, (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      , (∀ n : ℤ, b < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj K)) ∧
          ∀ (N : ModuleCat R) (i : ℤ), -a < i →
            ∀ e : Ext⁽i⁾(K, (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj K)) ∧
          ∀ (N : ModuleCat R),
            ∀ e : Ext⁽(-a + 1)⁾(K,
              (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      ])

end CategoryTheory
