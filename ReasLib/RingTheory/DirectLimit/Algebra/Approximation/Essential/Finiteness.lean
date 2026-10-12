/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Essential
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian consequences of essential-finite-type approximations

This leaf records the stagewise finiteness consequences of the property
bundle `Hom.EssFiniteType`.  The bundle itself remains independent of
Noetherian arguments, so consumers that only need the hypotheses can import
`Approximation.Essential` without importing this consequence layer.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit.Algebra.Approximation.Hom.EssFiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Every source stage in an essentially-finite-type approximation is
Noetherian. -/
@[stacks 00R1 "essential-finite-type approximation finiteness"]
theorem source_isNoetherianRing (A : Hom f) [A.EssFiniteType] (i : A.index) :
    IsNoetherianRing (A.source i) := sorry

/-- Every target stage in an essentially-finite-type approximation is
Noetherian. -/
@[stacks 00R1 "essential-finite-type approximation finiteness"]
theorem target_isNoetherianRing (A : Hom f) [A.EssFiniteType] (i : A.index) :
    IsNoetherianRing (A.target i) := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom.EssFiniteType
