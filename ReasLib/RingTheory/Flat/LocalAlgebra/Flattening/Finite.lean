/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening
public import ReasLib.RingTheory.LocalRing.Finite

@[expose] public section

universe u v w x

namespace LocalAlgCat.Flattening

variable (A : Type u) (B C : Type v) (M : Type w) (N : Type x)
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap B C)] [Module.Finite B C]
variable [AddCommGroup M] [Module B M]
variable [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

/-- If `B → C` is a finite local map of local `A`-algebras and `M ≃ₗ[B] N`,
then the flattening functors associated to `(B, M)` and `(C, N)` are equal. -/
theorem functor_eq_of_linearEquiv (e : M ≃ₗ[B] N) :
    functor A B M = functor A C N := sorry

end LocalAlgCat.Flattening
