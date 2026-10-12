/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module
import ReasLib.LinearAlgebra.QuotientByIdeal

universe u v w x

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [Algebra.EssFiniteType A B]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module.Flat A M]
variable (N : Type x) [AddCommGroup N] [Module B N] [Module A N]
variable [IsScalarTower A B N] [Module.Finite B N]
variable (u : N →ₗ[A] M)
variable (hbar : Function.Injective
  (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A)))

/- Situation 38.25.1: `A →+* B` is a local homomorphism of local rings that is
essentially of finite type, `M` is flat over `A`, `N` is finite over `B`, and the
`A`-linear map `u : N →ₗ[A] M` is injective after reducing modulo the maximal ideal of `A`. -/
@[stacks 0AT0] #check
  (LinearMap.quotientMapByIdeal u (IsLocalRing.maximalIdeal A) :
    N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) →ₗ[A]
      M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)))

#check (hbar : Function.Injective
  (LinearMap.quotientMapByIdeal u (IsLocalRing.maximalIdeal A)))

#check (algebraMap A B : A →+* B)
#check (inferInstance : IsLocalRing A)
#check (inferInstance : IsLocalRing B)
#check (inferInstance : IsLocalHom (algebraMap A B))
#check (inferInstance : Algebra.EssFiniteType A B)
#check (inferInstance : Module.Flat A M)
#check (inferInstance : Module.Finite B N)
#check (u : N →ₗ[A] M)

end
