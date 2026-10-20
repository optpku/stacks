/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring finiteness of directed approximations

This leaf contains only consequences of the ring-level `FiniteType`
approximation data.  Module finiteness is owned by
`Approximation.Module.Finiteness`.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit.Algebra.Approximation.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Every source stage of a finite-type approximation is Noetherian. -/
@[stacks 00R1 "finite-type approximation finiteness"]
theorem source_isNoetherianRing (A : FiniteType f) (i : A.index) :
    IsNoetherianRing (A.source i) := sorry

/-- Every target stage of a finite-type approximation is Noetherian. -/
@[stacks 00R1 "finite-type approximation finiteness"]
theorem target_isNoetherianRing (A : FiniteType f) (i : A.index) :
    IsNoetherianRing (A.target i) := sorry

/-- Every stage map of a finite-type approximation is finitely presented. -/
@[stacks 00R1 "finite-type approximation finiteness"]
theorem map_finitePresentation (A : FiniteType f) (i : A.index) :
    (A.map i).FinitePresentation := sorry

end Ring.DirectLimit.Algebra.Approximation.FiniteType
