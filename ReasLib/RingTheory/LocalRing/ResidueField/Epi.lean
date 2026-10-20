module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.RingTheory.Ideal.Quotient.Epi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue-field algebras are epimorphisms

@stack 00TT

The residue field is definitionally presented behind a named local-ring construction, so this
leaf supplies the canonical instance bridge that quotient instance search cannot see directly.
-/

@[expose] public section

universe u

namespace IsLocalRing.ResidueField

/-- The canonical residue map makes the residue field an epimorphic algebra over its local ring. -/
@[stacks 00TT "residue-field algebra epimorphism"]
instance instIsEpi (R : Type u) [CommRing R] [IsLocalRing R] :
    Algebra.IsEpi R (IsLocalRing.ResidueField R) :=
  inferInstanceAs <| Algebra.IsEpi R (R ⧸ IsLocalRing.maximalIdeal R)

end IsLocalRing.ResidueField

example (R : Type u) [CommRing R] [IsLocalRing R] :
    Algebra.IsEpi R (IsLocalRing.ResidueField R) :=
  inferInstance
