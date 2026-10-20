/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.IsTensorProduct
import StacksCheckRecall
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

/-!
# Definition 10.14.1 compatibility entry point

The base-changed algebra and module are recalled through Mathlib's tensor-product
and pushout API; `ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra` supplies
the opt-in right-oriented algebra instance used by the checks below.

@stack 05G4
-/

open scoped TensorProduct Algebra.TensorProduct.Right
open Algebra.TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {R' : Type w} [CommRing R'] [Algebra R R']

/- Definition 10.14.1 (Tag 05G4): for a ring map `R → S` and a ring map `R → R'`, the base change of
`R → S` by `R → R'` is the canonical `R`-algebra map `R' → S ⊗[R] R'`. -/
@[stacks 05G4 "base-changed algebra map"]
#check (includeRight : R' →ₐ[R] S ⊗[R] R')

/- The defining tensor-product square for the base-changed ring is the canonical pushout square
`R → S`, `R → R'`, `R' → S ⊗[R] R'`. -/
#check (TensorProduct.isPushout : Algebra.IsPushout R S R' (S ⊗[R] R'))

variable {M : Type x} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Definition 10.14.1 at the `core/canonical` owner layer: the base change of the `S`-module
`M` along `R → R'` is extension of scalars along `S → S ⊗[R] R'`, namely the canonical
`(S ⊗[R] R')`-module `(S ⊗[R] R') ⊗[S] M`. -/
#check ((S ⊗[R] R') ⊗[S] M)

/- The owner tensor product carries its natural module structure over the base-changed ring
`S ⊗[R] R'`. -/
#check (inferInstance : Module (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M))

#check (inferInstance : Module R' ((S ⊗[R] R') ⊗[S] M))
#check (inferInstance : IsScalarTower R' (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M))

/- The repeated unit map into the canonical base-change module is the existing mathlib tensor
map, rather than a source-specific wrapper. -/
#check (TensorProduct.mk S (S ⊗[R] R') M 1 : M →ₗ[S] (S ⊗[R] R') ⊗[S] M)
#check
  ((TensorProduct.mk S (S ⊗[R] R') M 1).restrictScalars R :
    M →ₗ[R] (S ⊗[R] R') ⊗[S] M)

/- At the `bridge/view` layer, the pushout owner abstraction identifies
`(S ⊗[R] R') ⊗[S] M` with the simpler
tensor model `R' ⊗[R] M`. -/
#check
  (Algebra.IsPushout.cancelBaseChange R R' S (S ⊗[R] R') M :
    ((S ⊗[R] R') ⊗[S] M) ≃ₗ[R'] R' ⊗[R] M)

/- The source-facing textbook presentation `M ⊗[R] R'` is the further tensor-symmetry view of
that canonical model. -/
#check (TensorProduct.comm R R' M : R' ⊗[R] M ≃ₗ[R] M ⊗[R] R')

end
