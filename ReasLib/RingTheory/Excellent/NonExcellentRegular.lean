module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.RingTheory.Excellent

@[expose] public section

universe u

open IsLocalRing

namespace IsRegularLocalRing

/-!
The function field of the projective plane over an algebraically closed field of
prime characteristic contains a non-excellent regular local ring whose residue
field has finite dimension over its canonical Frobenius subfield.
-/
/-- A non-excellent regular local ring with the stated function-field and
residue-field properties exists over every algebraically closed field of prime
characteristic. -/
@[stacks 0G67]
theorem exists_not_isExcellentRing_in_planeFunctionField
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
      (_ : IsRegularLocalRing A)
      (_ : Algebra A (FractionRing (MvPolynomial (Fin 2) k)))
      (_ : CharP (ResidueField A) p),
      IsFractionRing A (FractionRing (MvPolynomial (Fin 2) k)) ∧
        ¬ IsExcellentRing.{u, u} A ∧
        FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
          (ResidueField A) := sorry

end IsRegularLocalRing
