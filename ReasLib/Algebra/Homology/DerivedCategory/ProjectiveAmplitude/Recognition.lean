/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Recognizing projective amplitude by finite-presentation Ext tests

@stack 0G9A

For a pseudo-coherent derived object, projective amplitude is equivalent to perfectness with the
same Tor-amplitude and to the standard derived-Ext vanishing criteria tested on finitely
presented modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

namespace CategoryTheory

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Lemma 15.78.4 (0G9A): for a pseudo-coherent object `K` of `D(R)`, projective amplitude in
`[a, b]`, perfectness with Tor-amplitude in `[a, b]`, and the three standard derived-Ext
vanishing criteria on finitely presented `R`-modules are equivalent. -/
@[stacks 0G9A "projective amplitude recognized by finite-presentation Ext tests"]
theorem projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , K.IsPerfect ∧ DerivedCategory.HasTorAmplitudeIn (R := R) K a b
      , ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ),
          i ∉ Set.Icc (-b) (-a) →
            ∀ e : Ext⁽i⁾(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ), -a < i →
            ∀ e : Ext⁽i⁾(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R) [Module.FinitePresentation R N],
            ∀ e : Ext⁽(-a + 1)⁾(K, (single₀).obj N), e = 0
      ] := sorry

end CategoryTheory
