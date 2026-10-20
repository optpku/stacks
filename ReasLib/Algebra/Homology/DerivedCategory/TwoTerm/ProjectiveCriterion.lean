/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Recognition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projectivity criteria for two-term derived modules

This file owns the equivalence between projectivity of the surviving degree-zero cohomology and
degree-one Ext vanishing for objects supported in degrees `-1` and `0`.

@stack 0G9C
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

namespace CategoryTheory.DerivedCategory.TwoTerm

section

variable {R : Type u} [Ring R]

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "H" => _root_.DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" =>
  _root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Lemma 15.85.1: for a derived `R`-module supported in degrees `-1` and `0`, vanishing of
`H⁻¹(K)` together with projectivity of `H⁰(K)` is equivalent to vanishing of
`Ext¹_R(K, M)` for every `R`-module `M`. -/
@[stacks 0G9C "Lemma 15.85.1 (1)-(2)"]
theorem cohomology_projective_iff_extOne_vanishes
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      ∀ (M : ModuleCat R), ∀ e : Ext⁽(1 : ℤ)⁾(K, (single₀).obj M), e = 0 := sorry
/- Proof strategy: use the truncation triangle for an object in cohomological degrees `[-1, 0]`.
The long exact Ext sequence identifies the degree-one test with vanishing of `H⁻¹(K)` and the
usual projectivity criterion for `H⁰(K)`; discharge the endpoint terms using the supplied
`IsGE`/`IsLE` bounds and the projective-amplitude recognition API. -/

/-- The zero-functor form of the degree-one Ext criterion for a two-term derived module. -/
@[stacks 0G9C "degree-one Ext functor criterion"]
theorem cohomology_projective_iff_extOneFunctor_isZero
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      IsZero (_root_.CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor K (1 : ℤ)) := sorry
/- Proof strategy: combine `cohomology_projective_iff_extOne_vanishes` with the pointwise
characterization of a zero additive functor; evaluate the Ext functor on every module and identify
its elements with the displayed shifted Hom groups. -/

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "H" => _root_.DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" =>
  _root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Lemma 15.85.1, Noetherian case: when `H⁻¹(K)` and `H⁰(K)` are finite, the
projectivity condition and unrestricted degree-one Ext vanishing are also equivalent to testing
degree-one Ext only on finite modules. -/
@[stacks 0G9C "Lemma 15.85.1, Noetherian case"]
theorem cohomology_projective_extOne_tfae_of_noetherian
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    List.TFAE [
      IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K),
      ∀ (M : ModuleCat R), ∀ e : Ext⁽(1 : ℤ)⁾(K, (single₀).obj M), e = 0,
      ∀ (M : ModuleCat R), Module.Finite R M →
        ∀ e : Ext⁽(1 : ℤ)⁾(K, (single₀).obj M), e = 0
    ] := sorry
/- Proof strategy: obtain the equivalence of the first two conditions from
`cohomology_projective_iff_extOne_vanishes`.  The unrestricted condition implies the finite one;
for the converse, use Noetherian finiteness of `H⁻¹(K)` and `H⁰(K)` to apply the finite-module
Ext test for the associated coherent two-term functor, then assemble the three implications with
`List.tfae_finish`. -/

end

end CategoryTheory.DerivedCategory.TwoTerm
