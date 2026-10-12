/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.UpperRightBlock
import StacksCheckRecall

universe u

/- Example 42.68.22: for a field `k` and invertible `a × a` matrices `U` and `V`, the
determinant of the exact two-periodic complex with upper-right blocks `U` and `V` is the
residue-field image of `(-1) ^ a * det U / det V`. -/
@[stacks 02PS] #check
  (CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock.determinant_eq :
    ∀ {k : Type u} [Field k] {a : ℕ}
        (U V : Matrix.GeneralLinearGroup (Fin a) k),
      CategoryTheory.TwoPeriodicEndomorphism.determinant
          (CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock.complex U V)
          (CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock.complex_isFiniteLength
            U V)
          (CategoryTheory.TwoPeriodicEndomorphism.UpperRightBlock.complex_acyclic U V) =
        Units.map (IsLocalRing.residue k).toMonoidHom
          (((-1 : kˣ) ^ a) * Matrix.GeneralLinearGroup.det U /
            Matrix.GeneralLinearGroup.det V))
