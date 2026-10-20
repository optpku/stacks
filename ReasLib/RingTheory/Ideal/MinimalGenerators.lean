/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.RingTheory.RingHom.TorDimension

/-!
# Minimal generators of ideals in local rings

For an ideal `I` in a local ring, the quotient `I / 𝔪 I` is the linear
space controlling minimal generators.  Maps between these quotients are
expressed through the general `LinearMap.quotientMapByIdeal` API.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {I J : Ideal A}

/-- If `I ≤ J` are ideals in a Noetherian local ring, `J` is proper, and
`A / J` has finite Tor dimension over `A / I`, then the inclusion induces an
injection `I / 𝔪 I → J / 𝔪 J`. -/
@[stacks 09PV]
theorem quotientMapByMaximalIdeal_injective_of_finiteTorDimension
    (hJ : J ≠ ⊤) (hIJ : I ≤ J)
    (hTor : (Ideal.Quotient.factor hIJ).HasFiniteTorDimension) :
    Function.Injective
      ((Submodule.inclusion hIJ).quotientMapByIdeal
        (IsLocalRing.maximalIdeal A)) := sorry

end Ideal
