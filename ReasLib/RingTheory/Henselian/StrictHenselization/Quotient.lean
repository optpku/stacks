module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselian.Quotient
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.RingHom.IndEtale.Quotient
public import ReasLib.RingTheory.RingHom.Local.Quotient

@[expose] public section

/-!
# Quotients of Strict Henselizations

This leaf owns the compatibility of a chosen strict henselization with
quotienting the base by a proper ideal.  Its dependencies are the separate
quotient APIs for strictly henselian local rings, local maps, and ind-etale
maps; it has no dependency on a source chapter.

@stack 05WS
-/

universe u

namespace IsStrictHenselizationOf

variable {R Rsh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Tag `05WS`: quotienting a chosen strict henselization by the image of a
proper base ideal yields a strict henselization of the base quotient. -/
@[stacks 05WS "strict henselization proper quotient"]
theorem quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) := sorry

end IsStrictHenselizationOf
