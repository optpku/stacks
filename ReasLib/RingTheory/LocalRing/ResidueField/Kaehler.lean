module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.RingTheory.Kaehler.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# The conormal sequence of a residue-field quotient

@stack 00RU

This leaf exposes the quotient conormal map through the canonical
`ResidueField` definition, whose opacity otherwise prevents direct use of the
generic quotient-linear map in residue-field module categories.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace IsLocalRing.ResidueField

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- The quotient-linear conormal map for the residue-field quotient
`B → ResidueField B`. -/
@[stacks 00RU "residue-field conormal map"]
noncomputable def conormal :
    (maximalIdeal B).Cotangent →ₗ[ResidueField B]
      ResidueField B ⊗[B] Ω[B⁄A] :=
  KaehlerDifferential.Quotient.conormalToQuotient (R := A) (maximalIdeal B)

/-- The residue-field conormal map is exact before the Kähler base-change
map. -/
@[stacks 00RU "residue-field conormal exact sequence"]
theorem conormal_exact :
    Function.Exact conormal
      (KaehlerDifferential.mapBaseChange A B (ResidueField B)) := sorry

/-- The Kähler base-change map to the residue field is surjective. -/
@[stacks 0DYH "residue-field Kähler endpoint surjectivity"]
theorem mapBaseChange_surjective :
    Function.Surjective
      (KaehlerDifferential.mapBaseChange A B (ResidueField B)) := sorry

end IsLocalRing.ResidueField
