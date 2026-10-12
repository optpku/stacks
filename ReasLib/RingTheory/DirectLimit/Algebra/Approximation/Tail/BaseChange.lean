/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Properties
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-change properties on approximation tails

The core tail leaf owns only the restricted directed data.  This companion
owns the computations and transition properties that depend on the tensor
base-change API.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Surjectivity of all stage base-change maps is inherited by a cofinal tail. -/
@[stacks 00R1 "directed approximation tail base change"]
theorem tail_baseChange_surjective (A : Hom f)
    (hA : A.baseChange_surjective) (i₀ : A.index) :
    (A.tail i₀).baseChange_surjective := sorry

/-- Injectivity of all stage base-change maps is inherited by a cofinal tail. -/
@[stacks 00R1 "directed approximation tail base change"]
theorem tail_baseChange_injective (A : Hom f)
    (hA : A.baseChange_injective) (i₀ : A.index) :
    (A.tail i₀).baseChange_injective := sorry

/-- Bijectivity of all stage base-change maps is inherited by a cofinal tail. -/
@[stacks 00R1 "directed approximation tail base change"]
theorem tail_baseChange_bijective (A : Hom f)
    (hA : A.baseChange_bijective) (i₀ : A.index) :
    (A.tail i₀).baseChange_bijective := sorry

/-- The localization-of-quotient transition property is inherited by a
cofinal tail. -/
@[stacks 00R1 "directed approximation tail base change"]
theorem tail_baseChange_isLocalizationOfQuotient (A : Hom f)
    (hA : A.baseChange_isLocalizationOfQuotient) (i₀ : A.index) :
    (A.tail i₀).baseChange_isLocalizationOfQuotient := sorry

/-! Prime-localization witnesses are transported along the same tail map as
the underlying base-change map. -/

/-- The prime-localization transition property is inherited by a cofinal tail. -/
@[stacks 00R1 "directed approximation tail base change"]
theorem tail_baseChange_isLocalizationAtPrime (A : Hom f)
    (hA : A.baseChange_isLocalizationAtPrime) (i₀ : A.index) :
    (A.tail i₀).baseChange_isLocalizationAtPrime := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
