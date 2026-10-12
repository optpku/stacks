/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DirectSumDevissage.Basic
public import ReasLib.Algebra.Module.CountablyGenerated.Operations
public import ReasLib.Algebra.Module.CountablyGenerated.Submodule
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Projection
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.84.4

@stack 058X

The source theorem is the closure of internal direct sums of countably generated modules under
direct summands. The transfinite projection-stable block construction belongs to its proof, while
the split-map and complemented-submodule formulations form the reusable statement API.
-/

universe u v x

section

variable {R : Type u} [Ring R]
variable {M P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup P] [Module R P]

namespace Module

/-- A complemented submodule of an internal direct sum of countably generated submodules is again
an internal direct sum of countably generated submodules. -/
theorem isDirectSumOfCountablyGenerated_of_isCompl_submodule
    (A B : Submodule R M) (hAB : IsCompl A B)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R A := sorry

/-- Theorem 10.84.4: if `M` is an internal direct sum of countably generated `R`-submodules and
`P` is a direct summand of `M`, exhibited by split maps `i : P →ₗ[R] M` and `s : M →ₗ[R] P`,
then `P` is also an internal direct sum of countably generated submodules. -/
@[stacks 058X]
theorem directSummand_isDirectSumOfCountablyGenerated
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (hs : s.comp i = LinearMap.id)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := sorry

/-- The complemented-submodule form of Theorem 10.84.4. -/
theorem isDirectSumOfCountablyGenerated_of_isComplemented
    (P : Submodule R M) (hP : IsComplemented P)
    (hM : IsDirectSumOfCountablyGenerated.{u, v, x} R M) :
    IsDirectSumOfCountablyGenerated.{u, v, x} R P := sorry

end Module

end


@[stacks 058X "closure under direct summands"]
#check @Module.directSummand_isDirectSumOfCountablyGenerated

#check @Submodule.countablyGenerated_iff_subtype
#check @Module.CountablyGenerated.map
#check @Module.CountablyGenerated.of_linearEquiv
#check @Module.IsDirectSumOfCountablyGenerated.of_linearEquiv
