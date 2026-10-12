/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Map
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.RestrictScalars

/-!
# Surjective coefficient change for divided-power chain-DGA base change

Surjectivity of a coefficient algebra homomorphism is preserved after tensoring with an
arbitrary module.  Transporting this fact through explicit base-change models makes the
canonical semilinear coefficient-change map degreewise surjective.  The final statement is
also exposed as an ordinary divided-power map into the restricted target, which is the form
consumed by homology descent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uR uS uT uM uA

namespace TensorProduct

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T]
variable [Algebra R S] [Algebra R T]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- Applying a surjective algebra homomorphism to the left coefficient of a tensor product is
surjective. -/
theorem mapLeftAlgHom_surjective (sigma : S →ₐ[R] T)
    (h_sigma : Function.Surjective sigma) :
    Function.Surjective (mapLeftAlgHom (M := M) sigma) := sorry

end TensorProduct

namespace DividedPowerChainAlgebra.BaseChange

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {A : DividedPowerChainAlgebra.{uR, uA} R}

/-- Tag 09PQ: coefficient change between explicit divided-power chain-DGA base-change models is
degreewise surjective whenever the coefficient algebra homomorphism is surjective. -/
@[stacks 09PQ "surjective map between divided-power chain-DGA base changes"]
theorem map_surjective (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (h_sigma : Function.Surjective sigma) :
    (X.map sigma Y).Surjective := sorry

/-- The ordinary divided-power map into the scalar-restricted target obtained from a surjective
coefficient change is degreewise surjective in nonnegative degrees. -/
@[stacks 09PQ "surjective restricted-target base-change map"]
theorem map_toRestrictScalarsHom_surjective
    (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (h_sigma : Function.Surjective sigma) :
    (X.map sigma Y).toRestrictScalarsHom.Surjective := sorry

end DividedPowerChainAlgebra.BaseChange
