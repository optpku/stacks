/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.CohenMacaulay.Module.Local
public import ReasLib.RingTheory.Henselian.Henselization.Depth
public import ReasLib.RingTheory.Henselian.Henselization.KrullDimension
public import ReasLib.RingTheory.Henselian.Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohen-Macaulay local rings and henselization

The Cohen-Macaulay property of a Noetherian local ring is invariant under
henselization and strict henselization.

@stack 06LM
-/

@[expose] public section

universe u v w

namespace IsHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.9 (06LM): the Cohen-Macaulay property of a
Noetherian local ring, a henselization, and a strict henselization are
equivalent. -/
@[stacks 06LM "Cohen-Macaulayness under henselization"]
theorem cohenMacaulay_tfae
    [IsNoetherianRing Rh] [IsNoetherianRing Rsh] :
    List.TFAE
      [Module.CohenMacaulay R R, Module.CohenMacaulay Rh Rh,
        Module.CohenMacaulay Rsh Rsh] := sorry

end IsHenselizationOf

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- A Noetherian local ring is Cohen-Macaulay if and only if a
henselization is Cohen-Macaulay. -/
@[stacks 06LM "Cohen-Macaulayness under henselization"]
theorem cohenMacaulay_iff [IsNoetherianRing S] :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay S S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- A Noetherian local ring is Cohen-Macaulay if and only if a strict
henselization is Cohen-Macaulay. -/
@[stacks 06LM "Cohen-Macaulayness under strict henselization"]
theorem cohenMacaulay_iff [IsNoetherianRing S] :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay S S := sorry

end IsStrictHenselizationOf
