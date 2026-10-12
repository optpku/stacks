/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

/-!
# Tor-amplitude in a monoidal derived category

@stack 08FZ

This file defines Tor-amplitude using the canonical fixed-right derived tensor construction.
The definition applies to every monoidal abelian category for which unbounded derived tensoring
is available; module categories and module sheaves are specializations of this owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.DerivedTensor

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ (K L : CochainComplex C ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]
variable [Right.Has (C := C)]

/-- Objects whose derived tensor product with every degree-zero object lies in cohomological
degrees `≥ a`. -/
@[stacks 08FZ "(1), abstract lower-bound form"]
def torAmplitudeGE (a : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∀ M : C, (K ⊗ᴸ (DerivedCategory.singleFunctor C 0).obj M).IsGE a

/-- Object-level spelling of membership in the lower Tor-amplitude property. -/
abbrev HasTorAmplitudeGE (K : DerivedCategory C) (a : ℤ) : Prop :=
  torAmplitudeGE a K

/-- Objects whose derived tensor product with every degree-zero object lies in cohomological
degrees `≤ b`. -/
@[stacks 08FZ "(1), abstract upper-bound form"]
def torAmplitudeLE (b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∀ M : C, (K ⊗ᴸ (DerivedCategory.singleFunctor C 0).obj M).IsLE b

/-- Object-level spelling of membership in the upper Tor-amplitude property. -/
abbrev HasTorAmplitudeLE (K : DerivedCategory C) (b : ℤ) : Prop :=
  torAmplitudeLE b K

/-- The object property of having Tor-amplitude in `[a, b]`, tested against every degree-zero
object of the heart. -/
@[stacks 08FZ "(1), abstract monoidal form"]
def torAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  torAmplitudeGE a ⊓ torAmplitudeLE b

/-- Object-level spelling of membership in a fixed Tor-amplitude interval. -/
abbrev HasTorAmplitudeIn (K : DerivedCategory C) (a b : ℤ) : Prop :=
  torAmplitudeIn a b K

/-- The object property of having Tor-amplitude contained in some finite interval. -/
@[stacks 08FZ "(2), abstract monoidal form"]
def finiteTorDimension : ObjectProperty (DerivedCategory C) :=
  ⨆ a : ℤ, ⨆ b : ℤ, torAmplitudeIn a b

/-- Object-level spelling of membership in the finite-Tor-dimension property. -/
abbrev HasFiniteTorDimension (K : DerivedCategory C) : Prop :=
  finiteTorDimension K

/-- Heart objects whose degree-zero derived objects have Tor-amplitude in `[-d, 0]`. -/
@[stacks 08FZ "(4), abstract monoidal form"]
def torDimensionLE (d : ℕ) : ObjectProperty C :=
  fun M ↦ HasTorAmplitudeIn ((DerivedCategory.singleFunctor C 0).obj M) (-(d : ℤ)) 0

/-- Object-level spelling of having Tor dimension at most `d`. -/
abbrev HasTorDimensionLE (M : C) (d : ℕ) : Prop :=
  torDimensionLE (C := C) d M

/-- Tor-amplitude in `[a, b]` is equivalently the pair of its lower and upper bounds. -/
@[stacks 08FZ "Tor-amplitude as lower and upper bounds"]
theorem hasTorAmplitudeIn_iff (K : DerivedCategory C) (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeGE K a ∧ HasTorAmplitudeLE K b := sorry
/- Proof strategy: unfold `HasTorAmplitudeIn`, `torAmplitudeIn`, and membership in the infimum of
two object properties. -/

/-- Tor-amplitude in `[a, b]` is equivalently homology vanishing outside that interval after
derived tensoring with every degree-zero object. -/
@[stacks 08FZ "homology characterization of Tor-amplitude"]
theorem hasTorAmplitudeIn_iff_homology (K : DerivedCategory C) (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔
      ∀ (M : C) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor C i).obj
          (K ⊗ᴸ (DerivedCategory.singleFunctor C 0).obj M)) := sorry
/- Proof strategy: combine `hasTorAmplitudeIn_iff` with the t-structure characterizations of
`IsGE` and `IsLE`; outside `Set.Icc a b`, one of the two homology-vanishing conditions applies. -/

/-- A Tor-amplitude interval supplies its lower bound. -/
@[stacks 08FZ "Tor-amplitude lower-bound projection"]
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeGE K a := sorry
/- Proof strategy: apply the forward implication of `hasTorAmplitudeIn_iff` and take its first
component. -/

/-- A Tor-amplitude interval supplies its upper bound. -/
@[stacks 08FZ "Tor-amplitude upper-bound projection"]
theorem HasTorAmplitudeIn.hasTorAmplitudeLE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeLE K b := sorry
/- Proof strategy: apply the forward implication of `hasTorAmplitudeIn_iff` and take its second
component. -/

/-- Apply the lower bound of a Tor-amplitude interval to one test object. -/
@[stacks 08FZ "lower bound on a Tor-amplitude test object"]
theorem HasTorAmplitudeIn.tensorSingle_isGE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) (M : C) :
    (K ⊗ᴸ (DerivedCategory.singleFunctor C 0).obj M).IsGE a := sorry
/- Proof strategy: evaluate `hK.hasTorAmplitudeGE` at the test object `M`. -/

/-- Apply the upper bound of a Tor-amplitude interval to one test object. -/
@[stacks 08FZ "upper bound on a Tor-amplitude test object"]
theorem HasTorAmplitudeIn.tensorSingle_isLE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) (M : C) :
    (K ⊗ᴸ (DerivedCategory.singleFunctor C 0).obj M).IsLE b := sorry
/- Proof strategy: evaluate `hK.hasTorAmplitudeLE` at the test object `M`. -/

/-- A lower Tor-amplitude bound remains valid after lowering the bound. -/
@[stacks 08FZ "lower Tor-amplitude monotonicity"]
theorem HasTorAmplitudeGE.mono
    {K : DerivedCategory C} {a a' : ℤ} (hK : HasTorAmplitudeGE K a) (ha : a' ≤ a) :
    HasTorAmplitudeGE K a' := sorry
/- Proof strategy: evaluate `hK` on every test object and use monotonicity of the t-structure
lower bound along `ha`. -/

/-- An upper Tor-amplitude bound remains valid after raising the bound. -/
@[stacks 08FZ "upper Tor-amplitude monotonicity"]
theorem HasTorAmplitudeLE.mono
    {K : DerivedCategory C} {b b' : ℤ} (hK : HasTorAmplitudeLE K b) (hb : b ≤ b') :
    HasTorAmplitudeLE K b' := sorry
/- Proof strategy: evaluate `hK` on every test object and use monotonicity of the t-structure
upper bound along `hb`. -/

/-- A Tor-amplitude interval may be enlarged on either side. -/
@[stacks 08FZ "Tor-amplitude interval monotonicity"]
theorem HasTorAmplitudeIn.mono
    {K : DerivedCategory C} {a b a' b' : ℤ} (hK : HasTorAmplitudeIn K a b)
    (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn K a' b' := sorry
/- Proof strategy: project the lower and upper bounds, apply their two monotonicity theorems,
and recombine them through `hasTorAmplitudeIn_iff`. -/

/-- Lower Tor-amplitude is invariant under isomorphism in the derived category. -/
@[stacks 08FZ "lower Tor-amplitude under isomorphism"]
theorem HasTorAmplitudeGE.ofIso
    {K L : DerivedCategory C} {a : ℤ} (hK : HasTorAmplitudeGE K a) (e : K ≅ L) :
    HasTorAmplitudeGE L a := sorry
/- Proof strategy: map `e` through every fixed-right derived tensor functor and transport `IsGE`
across the resulting isomorphism. -/

/-- Upper Tor-amplitude is invariant under isomorphism in the derived category. -/
@[stacks 08FZ "upper Tor-amplitude under isomorphism"]
theorem HasTorAmplitudeLE.ofIso
    {K L : DerivedCategory C} {b : ℤ} (hK : HasTorAmplitudeLE K b) (e : K ≅ L) :
    HasTorAmplitudeLE L b := sorry
/- Proof strategy: map `e` through every fixed-right derived tensor functor and transport `IsLE`
across the resulting isomorphism. -/

/-- Tor-amplitude in a fixed interval is invariant under isomorphism in the derived category. -/
@[stacks 08FZ "Tor-amplitude interval under isomorphism"]
theorem HasTorAmplitudeIn.ofIso
    {K L : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) (e : K ≅ L) :
    HasTorAmplitudeIn L a b := sorry
/- Proof strategy: transport the lower and upper projections of `hK` with
`HasTorAmplitudeGE.ofIso` and `HasTorAmplitudeLE.ofIso`, then recombine them. -/

/-- Finite Tor dimension unfolds to the existence of a finite Tor-amplitude interval. -/
@[stacks 08FZ "finite Tor dimension as an interval"]
theorem hasFiniteTorDimension_iff (K : DerivedCategory C) :
    HasFiniteTorDimension K ↔ ∃ a b : ℤ, HasTorAmplitudeIn K a b := sorry
/- Proof strategy: unfold `HasFiniteTorDimension` and `finiteTorDimension`, then rewrite
membership in the two indexed suprema as existence of the two endpoints. -/

/-- Tor-amplitude in a fixed interval implies finite Tor dimension. -/
@[stacks 08FZ "Tor-amplitude implies finite Tor dimension"]
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {K : DerivedCategory C} {a b : ℤ} (hK : HasTorAmplitudeIn K a b) :
    HasFiniteTorDimension K := sorry
/- Proof strategy: apply `hasFiniteTorDimension_iff` and use `a`, `b`, and `hK` as the
witnesses. -/

/-- Finite Tor dimension is invariant under isomorphism in the derived category. -/
@[stacks 08FZ "finite Tor dimension under isomorphism"]
theorem HasFiniteTorDimension.ofIso
    {K L : DerivedCategory C} (hK : HasFiniteTorDimension K) (e : K ≅ L) :
    HasFiniteTorDimension L := sorry
/- Proof strategy: extract an interval witnessing `hK`, transport it with
`HasTorAmplitudeIn.ofIso`, and repackage the interval for `L`. -/

/-- Tor dimension at most `d` unfolds to the corresponding Tor-amplitude interval on the
degree-zero derived object. -/
@[stacks 08FZ "Tor dimension as a degree-zero Tor-amplitude interval"]
theorem hasTorDimensionLE_iff (M : C) (d : ℕ) :
    HasTorDimensionLE M d ↔
      HasTorAmplitudeIn ((DerivedCategory.singleFunctor C 0).obj M) (-(d : ℤ)) 0 := sorry
/- Proof strategy: unfold `HasTorDimensionLE` and `torDimensionLE`. -/

/-- A Tor-dimension bound remains valid after increasing the bound. -/
@[stacks 08FZ "Tor-dimension monotonicity"]
theorem HasTorDimensionLE.mono
    {M : C} {d e : ℕ} (hM : HasTorDimensionLE M d) (hde : d ≤ e) :
    HasTorDimensionLE M e := sorry
/- Proof strategy: rewrite both predicates with `hasTorDimensionLE_iff`, enlarge the lower
endpoint from `-d` to `-e` using `HasTorAmplitudeIn.mono`, and keep the upper endpoint zero. -/

/-- Tor dimension is invariant under isomorphism of heart objects. -/
@[stacks 08FZ "Tor dimension under isomorphism"]
theorem HasTorDimensionLE.ofIso
    {M N : C} {d : ℕ} (hM : HasTorDimensionLE M d) (e : M ≅ N) :
    HasTorDimensionLE N d := sorry
/- Proof strategy: map `e` with the degree-zero single functor, transport the resulting interval
using `HasTorAmplitudeIn.ofIso`, and rewrite with `hasTorDimensionLE_iff`. -/

/-- A fixed Tor-dimension bound is an isomorphism-closed object property. -/
@[stacks 08FZ "isomorphism stability of a Tor-dimension bound"]
instance torDimensionLE_isClosedUnderIsomorphisms (d : ℕ) :
    (torDimensionLE (C := C) d).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: package `HasTorDimensionLE.ofIso` as the object property's `of_iso` field. -/

/-- Lower Tor-amplitude is an isomorphism-closed object property. -/
@[stacks 08FZ "isomorphism stability of lower Tor-amplitude"]
instance torAmplitudeGE_isClosedUnderIsomorphisms (a : ℤ) :
    (torAmplitudeGE (C := C) a).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: package `HasTorAmplitudeGE.ofIso` as the object property's `of_iso` field. -/

/-- Upper Tor-amplitude is an isomorphism-closed object property. -/
@[stacks 08FZ "isomorphism stability of upper Tor-amplitude"]
instance torAmplitudeLE_isClosedUnderIsomorphisms (b : ℤ) :
    (torAmplitudeLE (C := C) b).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: package `HasTorAmplitudeLE.ofIso` as the object property's `of_iso` field. -/

/-- A fixed Tor-amplitude interval is closed under isomorphisms. -/
@[stacks 08FZ "isomorphism stability of a Tor-amplitude interval"]
instance torAmplitudeIn_isClosedUnderIsomorphisms (a b : ℤ) :
    (torAmplitudeIn (C := C) a b).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨hGE, hLE⟩
    exact ⟨HasTorAmplitudeGE.ofIso hGE e, HasTorAmplitudeLE.ofIso hLE e⟩

/-- Finite Tor dimension is closed under isomorphisms. -/
@[stacks 08FZ "isomorphism stability of finite Tor dimension"]
instance finiteTorDimension_isClosedUnderIsomorphisms :
    (finiteTorDimension (C := C)).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e hK
    exact HasFiniteTorDimension.ofIso hK e

end



end CategoryTheory.DerivedCategory.DerivedTensor
