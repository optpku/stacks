module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally Nilpotent Ideals in Noetherian Rings

In a Noetherian commutative semiring every ideal is finitely generated, so the
local condition of elementwise nilpotence is equivalent to nilpotence of the
ideal.  This leaf records that reusable upgrade without exposing a chosen
finite generating family.

@stack 00IM
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R] [IsNoetherianRing R]

namespace IsLocallyNilpotent

/-- Tag `00IM`: a locally nilpotent ideal in a Noetherian commutative
semiring is nilpotent. -/
@[stacks 00IM "Noetherian locally nilpotent ideal"]
theorem isNilpotent {I : Ideal R} (hI : I.IsLocallyNilpotent) :
    IsNilpotent I :=
  (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 hI

end IsLocallyNilpotent

/-- Tag `00IM`: over a Noetherian commutative semiring, local nilpotence of an
ideal is equivalent to nilpotence of the ideal. -/
@[stacks 00IM "Noetherian local nilpotence criterion"]
theorem isLocallyNilpotent_iff_isNilpotent (I : Ideal R) :
    I.IsLocallyNilpotent ↔ IsNilpotent I :=
  (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).symm

end Ideal
