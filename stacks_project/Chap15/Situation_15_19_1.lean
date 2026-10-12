/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import Mathlib.RingTheory.IsTensorProduct
import StacksCheckRecall

/-!
# Situation 15.19.1

@stack 05LP
-/

@[expose] public section

open Algebra.TensorProduct
open scoped TensorProduct Algebra.TensorProduct.Right
open Algebra.TensorProduct.Right

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable (J : Ideal S)

/- Situation 15.19.1 fixes an ideal `J ⊂ S` together with an `S`-module `M`; its underlying
`R`-module structure is the canonical restriction of scalars. -/
@[stacks 05LP "base-change setup"]
#check (Module.restrictScalars R S M : Module R M)

section

variable {R' : Type x} [CommRing R'] [Algebra R R']
variable [Module R M] [IsScalarTower R S M]

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- For a base change `R → R'`, the canonical owner ring is `S ⊗[R] R'`, the canonical owner
module is `((S ⊗[R] R') ⊗[S] M)`, and the source condition `(15.19.1.1)` is recalled separately
in `15_19_1_1`. The reusable base-change module map is owned by
mathlib's `TensorProduct.mk`, while Chapter `10`, Definition `10.14.1` is a source-facing
#check of the construction. Situation `15.19.1` reuses the canonical owner under the restricted-scalar
`R`-module structure and scalar tower on `M`; the textbook tensor model `M ⊗[R] R'` remains only
the bridge view of that owner. -/
#check (includeRight : R' →ₐ[R] S')
#check (TensorProduct.isPushout : Algebra.IsPushout R S R' S')
#check M'
#check (TensorProduct.mk S S' M 1 : M →ₗ[S] M')
#check ((TensorProduct.mk S S' M 1).restrictScalars R : M →ₗ[R] M')
#check (Algebra.IsPushout.cancelBaseChange R R' S S' M : M' ≃ₗ[R'] R' ⊗[R] M)
#check (TensorProduct.comm R R' M : R' ⊗[R] M ≃ₗ[R] M ⊗[R] R')

end

end
