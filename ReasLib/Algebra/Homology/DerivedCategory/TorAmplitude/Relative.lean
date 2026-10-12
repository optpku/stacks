/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative Tor amplitude and flat models

Tor amplitude along a ring map is Tor amplitude after derived restriction of scalars.  The
algebra-specialized model theorem separates the flatness assumption on the ring map from the
intrinsic predicates.

The current derived restriction-of-scalars owner uses universe-aligned `ModuleCat` categories,
so this derived predicate layer shares `u`.  The underlying module-level `FlatAlong` and raw
complex leaves are independent-universe APIs; this boundary is intentional rather than a
source-specific restriction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A]

/-- A derived `A`-module has Tor amplitude in `[a, b]` along `σ : R →+* A` when its derived
restriction to `R` has that Tor amplitude. -/
@[stacks 0E1U "Tor amplitude along a ring map"]
abbrev HasTorAmplitudeInAlong
    (σ : R →+* A) (K : DerivedCategory (ModuleCat A)) (a b : ℤ) : Prop :=
  HasTorAmplitudeIn R ((ModuleCat.derivedRestrictionOfScalars σ).obj K) a b

/-- A derived `A`-module has lower Tor-amplitude bound `a` along `σ : R →+* A` when its derived
restriction to `R` has that lower bound. -/
@[stacks 0E1U "lower Tor-amplitude bound along a ring map"]
abbrev HasTorAmplitudeGEAlong
    (σ : R →+* A) (K : DerivedCategory (ModuleCat A)) (a : ℤ) : Prop :=
  HasTorAmplitudeGE R ((ModuleCat.derivedRestrictionOfScalars σ).obj K) a

/-- A derived `A`-module has upper Tor-amplitude bound `b` along `σ : R →+* A` when its derived
restriction to `R` has that upper bound. -/
@[stacks 0E1U "upper Tor-amplitude bound along a ring map"]
abbrev HasTorAmplitudeLEAlong
    (σ : R →+* A) (K : DerivedCategory (ModuleCat A)) (b : ℤ) : Prop :=
  HasTorAmplitudeLE R ((ModuleCat.derivedRestrictionOfScalars σ).obj K) b

/-- A derived `A`-module object has finite Tor dimension along `σ : R →+* A` when its derived
restriction to `R` has finite Tor dimension. -/
@[stacks 0E1U "finite Tor dimension along a ring map"]
abbrev HasFiniteTorDimensionAlong
    (σ : R →+* A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  HasFiniteTorDimension R ((ModuleCat.derivedRestrictionOfScalars σ).obj K)

/-- Finite Tor dimension over a base algebra is finite Tor dimension along `algebraMap`. -/
@[stacks 0E1U "finite Tor dimension over a base algebra"]
abbrev HasFiniteTorDimensionOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) : Prop :=
  K.HasFiniteTorDimensionAlong (algebraMap R A)

/-- Tor amplitude over a base algebra is Tor amplitude along its algebra map. -/
@[stacks 0E1U "Tor amplitude over a base algebra"]
abbrev HasTorAmplitudeInOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) (a b : ℤ) : Prop :=
  K.HasTorAmplitudeInAlong (algebraMap R A) a b

/-- A lower Tor-amplitude bound over a base algebra is the corresponding bound along its algebra
map. -/
@[stacks 0E1U "lower Tor-amplitude bound over a base algebra"]
abbrev HasTorAmplitudeGEOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) (a : ℤ) : Prop :=
  K.HasTorAmplitudeGEAlong (algebraMap R A) a

/-- An upper Tor-amplitude bound over a base algebra is the corresponding bound along its algebra
map. -/
@[stacks 0E1U "upper Tor-amplitude bound over a base algebra"]
abbrev HasTorAmplitudeLEOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) (b : ℤ) : Prop :=
  K.HasTorAmplitudeLEAlong (algebraMap R A) b

/-- Finite Tor dimension along a ring map is the existence of a relative Tor-amplitude interval. -/
@[stacks 0E1U "finite relative Tor dimension as an interval"]
theorem hasFiniteTorDimensionAlong_iff
    (σ : R →+* A) (K : DerivedCategory (ModuleCat A)) :
    K.HasFiniteTorDimensionAlong σ ↔
      ∃ a b : ℤ, K.HasTorAmplitudeInAlong σ a b := sorry
/- Proof strategy: unfold the relative abbreviations and apply the absolute
`hasFiniteTorDimension_iff` theorem to the derived restriction of scalars of `K`. -/

/-- Finite Tor dimension over an algebra is the existence of a relative Tor-amplitude interval. -/
@[stacks 0E1U "finite Tor dimension over a base as an interval"]
theorem hasFiniteTorDimensionOver_iff
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) :
    K.HasFiniteTorDimensionOver R ↔
      ∃ a b : ℤ, K.HasTorAmplitudeInOver R a b := sorry
/- Proof strategy: specialize `hasFiniteTorDimensionAlong_iff` to `algebraMap R A` and unfold
the `Over` abbreviations. -/

/-- A lower Tor bound after restriction of scalars is a lower cohomological bound before
restriction. -/
@[stacks 0E1U "relative lower Tor bounds imply lower cohomological bounds"]
theorem HasTorAmplitudeGEAlong.isGE
    {σ : R →+* A} {K : DerivedCategory (ModuleCat A)} {a : ℤ}
    (hK : K.HasTorAmplitudeGEAlong σ a) : K.IsGE a := sorry
/- Proof strategy: the absolute lower Tor bound makes the restricted object `IsGE a`; reflect
the resulting homology vanishing through the exact faithful restriction-of-scalars functor. -/

/-- An upper Tor bound after restriction of scalars is an upper cohomological bound before
restriction. -/
@[stacks 0E1U "relative upper Tor bounds imply upper cohomological bounds"]
theorem HasTorAmplitudeLEAlong.isLE
    {σ : R →+* A} {K : DerivedCategory (ModuleCat A)} {b : ℤ}
    (hK : K.HasTorAmplitudeLEAlong σ b) : K.IsLE b := sorry
/- Proof strategy: the absolute upper Tor bound makes the restricted object `IsLE b`; reflect
the resulting homology vanishing through the exact faithful restriction-of-scalars functor. -/

/-- Algebra-map specialization of the lower cohomological bound supplied by relative Tor
amplitude. -/
@[stacks 0E1U "lower Tor bounds over a base imply lower cohomological bounds"]
theorem HasTorAmplitudeGEOver.isGE
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {K : DerivedCategory (ModuleCat A)} {a : ℤ}
    (hK : K.HasTorAmplitudeGEOver R a) : K.IsGE a := sorry
/- Proof strategy: specialize `HasTorAmplitudeGEAlong.isGE` to `algebraMap R A`. -/

/-- Algebra-map specialization of the upper cohomological bound supplied by relative Tor
amplitude. -/
@[stacks 0E1U "upper Tor bounds over a base imply upper cohomological bounds"]
theorem HasTorAmplitudeLEOver.isLE
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {K : DerivedCategory (ModuleCat A)} {b : ℤ}
    (hK : K.HasTorAmplitudeLEOver R b) : K.IsLE b := sorry
/- Proof strategy: specialize `HasTorAmplitudeLEAlong.isLE` to `algebraMap R A`. -/

end CategoryTheory.DerivedCategory
