/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Basic

@[expose] public section

/-!
# Universally Catenary Rings

This module owns universal catenarity and the immediate finite-type consequence.
Closure under further constructions belongs in separate leaf modules.
-/

universe u v w

section

variable (R : Type u) [CommRing R]

/-- A Noetherian ring is universally catenary when every finite type algebra over it is
catenary. -/
@[stacks 00NL]
class UniversallyCatenaryRing : Prop extends IsNoetherianRing R where
  /-- Every finite type algebra over a universally catenary ring is catenary. -/
  catenary_of_finiteType {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsCatenaryRing A

/-- A universally catenary ring is catenary by applying its defining property to itself. -/
instance instIsCatenaryRingOfUniversallyCatenaryRing [UniversallyCatenaryRing.{u, u} R] :
    IsCatenaryRing R := sorry

/-- Universal catenarity transports across ring equivalences. -/
theorem universallyCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [UniversallyCatenaryRing.{u, w} A] :
    UniversallyCatenaryRing.{v, w} B := sorry

end
