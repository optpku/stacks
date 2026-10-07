module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.DualNumber
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DualNumber

universe u

/- Example 42.68.19: for the regular dual-number module with differentials multiplication
by `uε` and `vε`, the periodic determinant is the residue of `-u / v`. -/
@[stacks 02PP] #check
  (CategoryTheory.TwoPeriodicEndomorphism.DualNumber.determinant_eq_neg_div :
    ∀ {k : Type u} [Field k] (u v : kˣ),
      CategoryTheory.TwoPeriodicEndomorphism.determinant
          (CategoryTheory.TwoPeriodicEndomorphism.DualNumber.complex u v)
          CategoryTheory.TwoPeriodicEndomorphism.DualNumber.regular_isFiniteLength
          (CategoryTheory.TwoPeriodicEndomorphism.DualNumber.complex_acyclic u v) =
        Units.map
          ((IsLocalRing.residue k[ε]).comp (algebraMap k k[ε])).toMonoidHom (-u / v))
