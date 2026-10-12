/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.FormallySmooth
public import ReasLib.RingTheory.Kaehler.Conormal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal maps for separable residue fields

This leaf is the field-theory bridge from Stacks-project separability of a
residue-field extension to the generic formally-smooth conormal API.

@stack 00TU
-/

@[expose] public section

universe u v

namespace Algebra.IsSeparableOver.Conormal

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]

/-- Tag `00TU`: if the residue field of a local `k`-algebra is separable over
`k`, its canonical conormal-to-Kaehler map is injective. -/
@[stacks 00TU "separable residue-field conormal injectivity"]
theorem residueField_injective
    [Algebra.IsSeparableOver k (IsLocalRing.ResidueField A)] :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A)) := by
  letI : Algebra.FormallySmooth k (IsLocalRing.ResidueField A) :=
    Algebra.formallySmooth_of_isSeparableOver
  exact KaehlerDifferential.Conormal.injective_of_formallySmooth
    (R := k) (P := A) (S := IsLocalRing.ResidueField A)
    ((IsLocalRing.ResidueField.algebraMap_eq A).symm ▸ IsLocalRing.residue_surjective)

end Algebra.IsSeparableOver.Conormal
