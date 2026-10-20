/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.RingTheory.Catenary.Local
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

/-!
# Cohen-Macaulay Criteria for Universal Catenarity

This leaf contains the reusable bridge from full-support locally
Cohen-Macaulay modules and Cohen-Macaulay rings to universal catenarity.
-/

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A locally Cohen-Macaulay module with full support makes its Noetherian base ring universally
catenary. -/
@[stacks 00NM]
theorem universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) :
    UniversallyCatenaryRing R := sorry

end

section

variable {R : Type u} [CommRing R]

/-- A Cohen-Macaulay ring is universally catenary. -/
theorem universallyCatenaryRing_of_cohenMacaulayRing (hCM : CohenMacaulayRing R) :
    UniversallyCatenaryRing R := sorry

end
