/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Decomposition
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced

/-!
# Dévissage of coherent module sheaves

This module records constructions of coherent module sheaves from ideal sheaves on integral
closed subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Let `X` be a Noetherian scheme, let `Z ⊆ X` be an integral closed subscheme with generic
point `ξ`, and let `ℱ` be a coherent `𝒪_X`-module whose stalk at the image of `ξ` is
annihilated by the maximal ideal. Then a finite coproduct of a coherent ideal sheaf on `Z`
admits a monic pushforward to `ℱ` which is an isomorphism near the image of `ξ`. -/
@[stacks 01YE]
theorem exists_coherentIdeal_coproduct_pushforward_mono_isIso_near_generic
    {X : Scheme.{u}} [IsNoetherian X]
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (ξ : Z.subscheme) (hξ : IsGenericPoint ξ (Set.univ : Set Z.subscheme))
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hξ_annihilated :
      ∀ a : X.presheaf.stalk (Z.subschemeι ξ),
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (Z.subschemeι ξ)) →
          ∀ m : (RingedSpace.stalkModuleCat ℱ (Z.subschemeι ξ)), a • m = 0) :
    ∃ (r : ℕ)
      (I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)),
      ∃ _ : (Subobject.underlying.obj I : Z.subscheme.Modules).IsCoherent,
      ∃ _ : ((Scheme.Modules.pushforward Z.subschemeι).obj
          (∐ fun _ : Fin r ↦ (Subobject.underlying.obj I : Z.subscheme.Modules))).IsCoherent,
      ∃ φ : ((Scheme.Modules.pushforward Z.subschemeι).obj
          (∐ fun _ : Fin r ↦ (Subobject.underlying.obj I : Z.subscheme.Modules))) ⟶ ℱ,
        Mono φ ∧ ∃ (U : X.Opens) (_ : Z.subschemeι ξ ∈ U), IsIso (φ |_ U) := sorry

/-- On a Noetherian scheme, every coherent module has a finite filtration by coherent
submodules whose successive quotients are pushforwards of nonzero coherent ideal sheaves on
integral closed subschemes. -/
@[stacks 01YF]
theorem exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal
    {X : Scheme.{u}} [IsNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent] :
    ∃ (m : ℕ) (F : ℕ →o Subobject ℱ)
      (Z : Fin m → X.IdealSheafData)
      (I : (j : Fin m) →
        Subobject (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules))
      (e : (j : Fin m) →
        cokernel (Subobject.ofLE (F j.1) (F (j.1 + 1)) (F.monotone (Nat.le_succ j.1))) ≅
          (Scheme.Modules.pushforward (Z j).subschemeι).obj
            (Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)),
      ∃ (hBot : F 0 = ⊥) (hTop : F m = ⊤)
        (hFiltrationCoherent :
          ∀ n : ℕ, n ≤ m → ((F n : Subobject ℱ) : X.Modules).IsCoherent)
        (hIntegral : ∀ j : Fin m, IsIntegral (Z j).subscheme)
        (hIdealCoherent : ∀ j : Fin m,
          ((Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)).IsCoherent),
        ∀ j : Fin m,
          I j ≠ (⊥ : Subobject
            (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules)) := sorry

/-- On a Noetherian scheme, a property of coherent module sheaves that contains zero, is
invariant under isomorphisms of coherent modules, is preserved by extensions, and holds for
pushforwards of quasicoherent ideal sheaves from integral closed subschemes holds for every
coherent module sheaf. -/
@[stacks 01YG]
theorem coherent_property_of_shortExact_and_pushforward_ideal
    {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_zero : P (0 : X.Modules))
    (h_iso : ∀ {ℱ 𝒢 : X.Modules}, ℱ.IsCoherent → 𝒢.IsCoherent →
      (ℱ ≅ 𝒢) → P ℱ → P 𝒢)
    (h_shortExact :
      ∀ {S : ShortComplex X.Modules}, S.ShortExact →
        S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
        P S.X₁ → P S.X₃ → P S.X₂)
    (h_pushforward_ideal :
      ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
        (I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)),
        (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules)))
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

/-- A property of module sheaves is preserved by short exact extensions of coherent modules. -/
def DevissageShortExactClosed {X : Scheme.{u}} (P : X.Modules → Prop) : Prop :=
  ∀ {S : ShortComplex X.Modules}, S.ShortExact →
    S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
    P S.X₁ → P S.X₃ → P S.X₂

/-- Short-exact closure is equivalent to preservation by every coherent short exact
extension. -/
theorem devissageShortExactClosed_iff {X : Scheme.{u}} (P : X.Modules → Prop) :
    DevissageShortExactClosed P ↔
      ∀ {S : ShortComplex X.Modules}, S.ShortExact →
        S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
        P S.X₁ → P S.X₃ → P S.X₂ := Iff.rfl

/-- A property of coherent module sheaves descends from every nonempty finite self-coproduct. -/
def DevissageDescendsFromFiniteCoproducts {X : Scheme.{u}} (P : X.Modules → Prop) : Prop :=
  ∀ (ℱ : X.Modules), ℱ.IsCoherent → ∀ (r : ℕ), 0 < r →
    P (∐ fun _ : Fin r ↦ ℱ) → P ℱ

/-- Descent from finite self-coproducts is equivalent to descent for every coherent module and
every positive number of summands. -/
theorem devissageDescendsFromFiniteCoproducts_iff
    {X : Scheme.{u}} (P : X.Modules → Prop) :
    DevissageDescendsFromFiniteCoproducts P ↔
      ∀ (ℱ : X.Modules), ℱ.IsCoherent → ∀ (r : ℕ), 0 < r →
        P (∐ fun _ : Fin r ↦ ℱ) → P ℱ := Iff.rfl

/-- A property holds for pushforwards of quasicoherent ideal sheaves from every integral closed
subscheme whose support is properly contained in a fixed irreducible closed subset. -/
def DevissageHoldsOnProperIntegralIdealPushforwards
    {X : Scheme.{u}} (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (P : X.Modules → Prop) : Prop :=
  ∀ (Z : X.IdealSheafData), IsIntegral Z.subscheme →
    (Z.support : Set X) ⊂ (Z₀ : Set X) →
      ∀ I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
        (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules))

/-- The ideal-pushforward condition is equivalent to its value on every quasicoherent ideal
sheaf over every integral closed subscheme with properly smaller support. -/
theorem devissageHoldsOnProperIntegralIdealPushforwards_iff
    {X : Scheme.{u}} (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (P : X.Modules → Prop) :
    DevissageHoldsOnProperIntegralIdealPushforwards Z₀ P ↔
      ∀ (Z : X.IdealSheafData), IsIntegral Z.subscheme →
        (Z.support : Set X) ⊂ (Z₀ : Set X) →
          ∀ I : Subobject
              (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
            (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
              P ((Scheme.Modules.pushforward Z.subschemeι).obj
                (Subobject.underlying.obj I : Z.subscheme.Modules)) := Iff.rfl

/-- A generic model for an irreducible closed subset is a coherent module supported exactly on
that subset, annihilated generically by the maximal ideal, and admitting property-bearing
quasicoherent submodules inside every ideal multiple which is generically the whole module. -/
def DevissageGenericModel
    {X : Scheme.{u}} (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (ξ : X) (P : X.Modules → Prop) : Prop :=
  ∃ (𝒢 : X.Modules) (coherent : 𝒢.IsCoherent),
    moduleSupport 𝒢 = (Z₀ : Set X) ∧
      (∀ a : X.presheaf.stalk ξ,
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
          ∀ m : RingedSpace.stalkModuleCat 𝒢 ξ, a • m = 0) ∧
      ∀ J : X.IdealSheafData, ξ ∉ (J.support : Set X) →
        ∃ 𝒢' : Subobject 𝒢,
          (𝒢' : X.Modules).IsQuasicoherent ∧
            𝒢' ≤ idealPowerProductSubobject J 𝒢 1 ∧
            ξ ∉ moduleSupport (cokernel 𝒢'.arrow) ∧
            P (𝒢' : X.Modules)

/-- The generic-model condition is equivalent to the existence of a coherent model satisfying
the stated support, annihilation, ideal-multiple, generic-agreement, and property conditions. -/
theorem devissageGenericModel_iff
    {X : Scheme.{u}} (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (ξ : X) (P : X.Modules → Prop) :
    DevissageGenericModel Z₀ ξ P ↔
      ∃ (𝒢 : X.Modules) (coherent : 𝒢.IsCoherent),
        moduleSupport 𝒢 = (Z₀ : Set X) ∧
          (∀ a : X.presheaf.stalk ξ,
            a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
              ∀ m : RingedSpace.stalkModuleCat 𝒢 ξ, a • m = 0) ∧
          ∀ J : X.IdealSheafData, ξ ∉ (J.support : Set X) →
            ∃ 𝒢' : Subobject 𝒢,
              (𝒢' : X.Modules).IsQuasicoherent ∧
                𝒢' ≤ idealPowerProductSubobject J 𝒢 1 ∧
                ξ ∉ moduleSupport (cokernel 𝒢'.arrow) ∧
                P (𝒢' : X.Modules) := Iff.rfl

/-- On a Noetherian scheme, an extension-closed property which descends from nonempty finite
self-coproducts, holds for ideal pushforwards from proper integral closed subsets, and has a
generic model holds for every coherent module supported on the fixed irreducible closed
subset. -/
@[stacks 01YL]
theorem devissage_property_of_support_subset_irreducibleClosed
    {X : Scheme.{u}} [IsNoetherian X]
    (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (ξ : X) (hξ : IsGenericPoint ξ (Z₀ : Set X))
    (P : X.Modules → Prop)
    (h_shortExact : DevissageShortExactClosed P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_proper_closed : DevissageHoldsOnProperIntegralIdealPushforwards Z₀ P)
    (h_generic_model : DevissageGenericModel Z₀ ξ P)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSupp : moduleSupport ℱ ⊆ (Z₀ : Set X)) :
    P ℱ := sorry

/-- On a nonempty Noetherian scheme, an extension-closed property which descends from
nonempty finite self-coproducts and admits a generic model on every irreducible closed
subset holds for every coherent module sheaf. -/
@[stacks 01YM]
theorem devissagePropertyHoldsOfIntegralClosedGenericModels
    {X : Scheme.{u}} [Nonempty X] [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_shortExact : DevissageShortExactClosed P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_generic :
      ∀ (Z₀ : TopologicalSpace.IrreducibleCloseds X) (ξ : X),
        IsGenericPoint ξ (Z₀ : Set X) → DevissageGenericModel Z₀ ξ P)
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

/-- A property of coherent module sheaves satisfies two-out-of-three for short exact sequences. -/
structure DevissageTwoOutOfThree
    {X : Scheme.{u}} (P : X.Modules → Prop) : Prop where
  /-- If the left and middle terms satisfy the property, then so does the right term. -/
  right_of_left_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₁ : P S.X₁) (hP₂ : P S.X₂) : P S.X₃
  /-- If the left and right terms satisfy the property, then so does the middle term. -/
  middle_of_left_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₁ : P S.X₁) (hP₃ : P S.X₃) : P S.X₂
  /-- If the middle and right terms satisfy the property, then so does the left term. -/
  left_of_middle_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hP₂ : P S.X₂) (hP₃ : P S.X₃) : P S.X₁

/-- A module property satisfies two-out-of-three for coherent short exact sequences whose terms
are supported on a fixed closed subscheme. -/
structure DevissageTwoOutOfThreeOnSupport
    {X : Scheme.{u}} (Z₀ : X.IdealSheafData) (P : X.Modules → Prop) : Prop where
  /-- If the left and middle terms satisfy the property, then so does the right term. -/
  right_of_left_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₁ : P S.X₁) (hP₂ : P S.X₂) : P S.X₃
  /-- If the left and right terms satisfy the property, then so does the middle term. -/
  middle_of_left_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₁ : P S.X₁) (hP₃ : P S.X₃) : P S.X₂
  /-- If the middle and right terms satisfy the property, then so does the left term. -/
  left_of_middle_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₂ : P S.X₂) (hP₃ : P S.X₃) : P S.X₁

/-- Restrict a global two-out-of-three law to modules supported on a closed subscheme. -/
def DevissageTwoOutOfThree.onSupport
    {X : Scheme.{u}} {P : X.Modules → Prop} (hP : DevissageTwoOutOfThree P)
    (Z₀ : X.IdealSheafData) :
    DevissageTwoOutOfThreeOnSupport Z₀ P where
  right_of_left_middle hS h₁ h₂ h₃ _ _ _ hP₁ hP₂ :=
    hP.right_of_left_middle hS h₁ h₂ h₃ hP₁ hP₂
  middle_of_left_right hS h₁ h₂ h₃ _ _ _ hP₁ hP₃ :=
    hP.middle_of_left_right hS h₁ h₂ h₃ hP₁ hP₃
  left_of_middle_right hS h₁ h₂ h₃ _ _ _ hP₂ hP₃ :=
    hP.left_of_middle_right hS h₁ h₂ h₃ hP₂ hP₃

/-- Restrict a support-relative two-out-of-three law along an inclusion of closed supports. -/
def DevissageTwoOutOfThreeOnSupport.restrict
    {X : Scheme.{u}} {Z₀ Z₁ : X.IdealSheafData} {P : X.Modules → Prop}
    (hP : DevissageTwoOutOfThreeOnSupport Z₀ P)
    (hZ : (Z₁.support : Set X) ⊆ (Z₀.support : Set X)) :
    DevissageTwoOutOfThreeOnSupport Z₁ P where
  right_of_left_middle hS h₁ h₂ h₃ hSupp₁ hSupp₂ hSupp₃ hP₁ hP₂ :=
    hP.right_of_left_middle hS h₁ h₂ h₃ (hSupp₁.trans hZ) (hSupp₂.trans hZ)
      (hSupp₃.trans hZ) hP₁ hP₂
  middle_of_left_right hS h₁ h₂ h₃ hSupp₁ hSupp₂ hSupp₃ hP₁ hP₃ :=
    hP.middle_of_left_right hS h₁ h₂ h₃ (hSupp₁.trans hZ) (hSupp₂.trans hZ)
      (hSupp₃.trans hZ) hP₁ hP₃
  left_of_middle_right hS h₁ h₂ h₃ hSupp₁ hSupp₂ hSupp₃ hP₂ hP₃ :=
    hP.left_of_middle_right hS h₁ h₂ h₃ (hSupp₁.trans hZ) (hSupp₂.trans hZ)
      (hSupp₃.trans hZ) hP₂ hP₃

/-- A coherent module sheaf supported exactly on a fixed closed subscheme, killed generically
by the maximal ideal, with one-dimensional generic residue fiber, and satisfying a property. -/
structure DevissageGenericRankOneSheaf
    {X : Scheme.{u}} (Z₀ : X.IdealSheafData) (ξ : X)
    (P : X.Modules → Prop) (𝒢 : X.Modules) : Prop where
  /-- The generic model is coherent. -/
  coherent : 𝒢.IsCoherent
  /-- The support is exactly the fixed closed subscheme support. -/
  support_eq : moduleSupport 𝒢 = (Z₀.support : Set X)
  /-- The maximal ideal at the generic point annihilates the stalk. -/
  maximalIdeal_smul_eq_zero
    (a : X.presheaf.stalk ξ)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ))
    (m : RingedSpace.stalkModuleCat 𝒢 ξ) : a • m = 0
  /-- The generic residue-field fiber has dimension one. -/
  fiber_finrank_eq_one : Scheme.Modules.fiberFinrank 𝒢 ξ = 1
  /-- The generic model satisfies the property. -/
  property : P 𝒢

/-- Transport the property carried by a generic rank-one sheaf along a pointwise implication. -/
def DevissageGenericRankOneSheaf.map_property
    {X : Scheme.{u}} {Z₀ : X.IdealSheafData} {ξ : X}
    {P Q : X.Modules → Prop} {𝒢 : X.Modules}
    (h𝒢 : DevissageGenericRankOneSheaf Z₀ ξ P 𝒢)
    (hPQ : ∀ ℰ : X.Modules, P ℰ → Q ℰ) :
    DevissageGenericRankOneSheaf Z₀ ξ Q 𝒢 where
  coherent := h𝒢.coherent
  support_eq := h𝒢.support_eq
  maximalIdeal_smul_eq_zero := h𝒢.maximalIdeal_smul_eq_zero
  fiber_finrank_eq_one := h𝒢.fiber_finrank_eq_one
  property := hPQ 𝒢 h𝒢.property

/-- On a Noetherian scheme, a support-relative two-out-of-three property which holds for ideal
pushforwards from proper integral closed subsets and for a generically rank-one coherent model
holds for every coherent module supported on the fixed integral closed subscheme. -/
@[stacks 01YH]
theorem devissagePropertyHoldsOfIdealPushforwardsAndGenericRankOne
    {X : Scheme.{u}} [IsNoetherian X]
    (Z₀ : X.IdealSheafData) [IsIntegral Z₀.subscheme]
    (ξ : X) (hξ : IsGenericPoint ξ (Z₀.support : Set X))
    (P : X.Modules → Prop)
    (hP_shortExact : DevissageTwoOutOfThreeOnSupport Z₀ P)
    (hP_ideal :
      ∀ (Z : X.IdealSheafData) [IsIntegral Z.subscheme],
        (Z.support : Set X) ⊂ (Z₀.support : Set X) →
        ∀ I : Subobject
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
          (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules)))
    (hP_generic :
      ∃ 𝒢 : X.Modules,
        DevissageGenericRankOneSheaf Z₀ ξ P 𝒢)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppℱ : moduleSupport ℱ ⊆ (Z₀.support : Set X)) :
    P ℱ := sorry

/-- On a nonempty Noetherian scheme, a two-out-of-three property of coherent module sheaves
holds universally if every integral closed subscheme has a property-bearing coherent model
of generic rank one with exactly that support. -/
@[stacks 01YI]
theorem devissagePropertyHoldsOfGenericRankOneSheaves
    {X : Scheme.{u}} [Nonempty X] [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_shortExact : DevissageTwoOutOfThree P)
    (h_generic :
      ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
        (ξ : X), IsGenericPoint ξ (Z.support : Set X) →
          ∃ 𝒢 : X.Modules, DevissageGenericRankOneSheaf Z ξ P 𝒢)
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
