module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.Quotient
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.LocalRing.ResidueField.Quotient
public import ReasLib.RingTheory.RingHom.IndEtale.Quotient
public import ReasLib.RingTheory.RingHom.Local.Quotient

@[expose] public section

/-!
# Quotients of Henselizations

This leaf owns the compatibility of a chosen henselization with quotienting
the base by a proper ideal.  Its proof assembles the independent quotient APIs
for henselian local rings, local maps, ind-etale maps, and residue fields.
The same-universe restriction is intrinsic to the available raw ind-etale
quotient presentation.

@stack 05WQ
-/

universe u

namespace IsHenselizationOf

variable {R Rh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- Tag `05WQ`: quotienting a chosen henselization by the image of a proper
base ideal yields a henselization of the base quotient. -/
@[stacks 05WQ "henselization proper quotient"]
theorem quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) := sorry

end IsHenselizationOf
