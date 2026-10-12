/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Excellent.NonExcellentRegular
import StacksCheckRecall

universe u

open IsLocalRing

/- Remark 110.44.3: non-excellent regular local rings whose residue fields have a finite
`p`-basis can be constructed even in the function field of `ℙ²` over an algebraically closed
field `k` of characteristic `p`. The function field of `ℙ²` is identified with
`FractionRing (MvPolynomial (Fin 2) k)`. See DS18, §4.1. -/
@[stacks 0G67] #check (IsRegularLocalRing.exists_not_isExcellentRing_in_planeFunctionField :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p],
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A)
      (_ : IsRegularLocalRing A)
      (_ : Algebra A (FractionRing (MvPolynomial (Fin 2) k)))
      (_ : CharP (ResidueField A) p),
      IsFractionRing A (FractionRing (MvPolynomial (Fin 2) k)) ∧
        ¬ IsExcellentRing.{u, u} A ∧
        FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
          (ResidueField A))
