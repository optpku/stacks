module

public import ReasLib.Algebra.Module.IdealProjective.Ext
public import ReasLib.CategoryTheory.Linear.IdealProjective.ShortExact

@[expose] public section

/-!
# Projective-factor ideals in short exact sequences

@stack 0G95

The strongest module-level form compares the projective-factor ideals of the quotient and kernel
terms.  The usual ideal-projectivity statement follows by transitivity.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{max u v} R)}

/-- Across a short exact sequence with projective middle term, the projective-factor ideal of
the quotient is contained in that of the kernel. -/
@[stacks 0G95 "projective-factor ideal of a syzygy"]
theorem projectiveFactorIdeal_le_X₁ (hS : S.ShortExact) [Projective S.X₂] :
    Module.projectiveFactorIdeal R S.X₃ ≤ Module.projectiveFactorIdeal R S.X₁ := sorry

/-- Lemma 15.71.6: the kernel of a projective presentation of an ideal-projective module is
ideal-projective. -/
@[stacks 0G95 "ideal-projectivity of a syzygy"]
theorem isIdealProjective_X₁ {I : Ideal R} (hS : S.ShortExact)
    (hX₃ : Module.IsIdealProjective I S.X₃) [Projective S.X₂] :
    Module.IsIdealProjective I S.X₁ := sorry

end CategoryTheory.ShortComplex.ShortExact
