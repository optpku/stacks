module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Flatness of henselian extensions

The flatness consequences of henselian and strict-henselian constructions are kept here as
standalone interfaces.  Normalization and completion modules can use these facts without
importing a chapter file.

@stack 04GN
@stack 04GP
-/

open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

namespace IsHenselizationOf

variable [IsHenselizationOf R S]

/-- A henselization is flat over its local base ring. -/
@[stacks 04GN "flatness of a Henselization"]
theorem moduleFlat : Module.Flat R S := sorry

end IsHenselizationOf

/-- An ind-etale local algebra map is flat over its base ring. -/
@[stacks 04GN "flatness of an ind-etale local algebra"]
theorem moduleFlat_of_indEtale
    (hcolim : RingHom.IndEtale.Raw (algebraMap R S)) :
    Module.Flat R S := sorry

end
