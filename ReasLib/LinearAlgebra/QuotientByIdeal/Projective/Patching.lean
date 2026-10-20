module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
import ReasLib.LinearAlgebra.QuotientByIdeal.Endomorphism
import ReasLib.LinearAlgebra.Quotient.Pair
import Mathlib.Tactic.CrossRefAttribute

/-!
# Patching projective modules from two quotient reductions

Projectivity of a module can be patched from its reductions modulo two two-sided ideals with zero
intersection. The statement is owned by `Module.Projective`; paired-quotient and endomorphism
arguments are imported only as proof infrastructure.

@stack 0H7M
-/

@[expose] public section

universe u v

namespace Module.Projective

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- A module is projective if its reductions modulo two two-sided ideals with zero intersection
are projective over the corresponding quotient rings. -/
@[stacks 0H7M]
theorem of_quotients_of_inf_eq_bot (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    Module.Projective R P := sorry

end Module.Projective
