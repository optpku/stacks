module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RegularLocalRing.Parameters
public import ReasLib.RingTheory.Sequence.Regularity

/-!
# Flatness from Regular Parameters

@stack 07DY

This leaf owns the local flatness criterion obtained when a regular system of
parameters maps to a regular sequence in the target.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Module.Flat

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

include S

/-- Stacks 07DY: a local algebra over a regular local ring is flat when a regular system of
parameters of the source maps to a regular sequence in the target. -/
@[stacks 07DY "flatness from a regular system of parameters"]
theorem of_regularSystemOfParameters_image_isRegular
    {d : ℕ} (x : Fin d → maximalIdeal R)
    (hx : IsRegularSystemOfParameters x)
    (hreg : RingTheory.Sequence.IsRegular S
      (List.ofFn fun i ↦ algebraMap R S (x i : R))) :
    Module.Flat R S := sorry

omit S

end Module.Flat
