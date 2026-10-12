/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties
import Mathlib.Tactic.CrossRefAttribute

/-!
# Singleton systems of parameters

This leaf records the one-element bridges between the cotangent-space criterion, partial regular
systems of parameters, and principal ideals.

@stack 07PF
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- The parameter ideal of a singleton family is the corresponding principal ideal. -/
@[stacks 07PF "singleton parameter ideal"]
theorem parameterIdeal_finOne_eq_principalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] (x : maximalIdeal R) :
    parameterIdeal (fun _ : Fin 1 ↦ x) = principalIdeal (x : R) := sorry

/-- In a regular local ring, an element outside `𝔪 ^ 2` is a one-element partial regular system
of parameters. -/
@[stacks 07PF "singleton partial system of parameters"]
theorem isPartOfRegularSystemOfParameters_singleton
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (x : maximalIdeal R)
    (hx : (x : R) ∉ maximalIdeal R ^ 2) :
    IsPartOfRegularSystemOfParameters (maximalIdeal R).spanFinrank
      (fun _ : Fin 1 ↦ x) := sorry

end IsLocalRing
