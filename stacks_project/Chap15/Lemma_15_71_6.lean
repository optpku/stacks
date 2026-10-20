module

public import ReasLib.Algebra.Module.IdealProjective.ShortExact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.6

@stack 0G95
-/

/-!
# Lemma 15.71.6: ideal-projective syzygies
-/

/- Lemma 15.71.6: in a short exact sequence with projective middle term, ideal-projectivity of
the quotient implies ideal-projectivity of the kernel. -/
@[stacks 0G95]
#check @CategoryTheory.ShortComplex.ShortExact.isIdealProjective_X₁

/- Strong module form, comparing the complete projective-factor ideals. -/
#check @CategoryTheory.ShortComplex.ShortExact.projectiveFactorIdeal_le_X₁

/- Generic linear-abelian form. -/
#check @CategoryTheory.ShortComplex.ShortExact.idealProjective_X₁

/- Symmetric extension-class obstruction APIs used by the generic theorem. -/
#check @CategoryTheory.ShortComplex.ShortExact.mk₀_comp_extClass_eq_zero_iff
#check @CategoryTheory.ShortComplex.ShortExact.extClass_comp_mk₀_eq_zero_iff
