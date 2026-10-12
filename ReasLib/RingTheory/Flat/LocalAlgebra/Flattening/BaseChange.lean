/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Flat.BaseChange
public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening

/-!
# Base change of local-algebra flattening functors

This module records invariance of closed-point flatness and its associated flattening functor
under flat local extension of the coefficient algebra.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B C : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap B C)] [Module.Flat B C]
variable [AddCommGroup M] [Module B M]

namespace IsFlatAtClosedPoint

/-- Closed-point flatness is unchanged after extending scalars along a flat local map
`B ⟶ C` of local `A`-algebras. -/
theorem iff_baseChange (T : LocalAlgCat.{v} A) :
    IsFlatAtClosedPoint A B M T ↔
      IsFlatAtClosedPoint A C (C ⊗[B] M) T := sorry

end IsFlatAtClosedPoint

/-- Extending a module along a flat local map `B ⟶ C` of local `A`-algebras does not change
its flattening functor. -/
theorem functor_eq_baseChange :
    functor A B M = functor A C (C ⊗[B] M) := sorry

end LocalAlgCat.Flattening
