/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.ShiftPower
public import ReasLib.RingTheory.RingHom.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for shift-power generation

@stack 09EF

This leaf contains the tensor-product transport of shift-power generation. Its
primary API takes the two ring homomorphisms defining the base change.
-/

@[expose] public section

universe u v w

namespace RingHom

namespace ShiftPower

namespace BaseChange

/-- Shift-power generation is preserved by tensor-product base change along an arbitrary ring
homomorphism. -/
@[stacks 09EF]
theorem isGenerated
    {R : Type u} {S : Type v} {R' : Type w}
    [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : IsGenerated f) :
    IsGenerated (f.baseChange g) := sorry

/-- Ambient-algebra specialization of the BaseChange.isGenerated theorem. -/
theorem isGenerated_algebraMap
    {R : Type u} {S : Type v} {R' : Type w}
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R R']
    (f : R →+* S) (hgen : IsGenerated f) :
    IsGenerated (f.baseChangeAlgebraMap (R' := R')) := sorry

end BaseChange

end ShiftPower

end RingHom
