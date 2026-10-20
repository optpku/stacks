/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra.Functor

/-!
# Zeroth homology algebras of chain DGAs

This file exposes zeroth homology as the degree-zero algebra of the canonical graded homology
algebra.  Its map API is inherited functorially from graded homology, so downstream constructions
do not need a separate chosen realization of `H₀`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The canonical zeroth homology algebra of a strictly commutative chain DGA. -/
@[stacks 09PK "zeroth homology algebra"]
noncomputable abbrev homologyZero (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] : Type v :=
  A.homologyNonnegativePart.degreeZero

/-- The unit of the canonical zeroth homology algebra is the class of the chain-level unit. -/
@[simp] theorem homologyZero_one (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    (1 : A.homologyZero) = A.homologyOne := sorry

/-- Multiplication in the canonical zeroth homology algebra is homology multiplication in degree
zero. -/
@[simp] theorem homologyZero_mul (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (x y : A.homologyZero) :
    x * y = A.homologyMul 0 0 x y := sorry

/-- The structural map of the canonical zeroth homology algebra is the homology scalar map. -/
@[simp] theorem homologyZero_algebraMap (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    (r : R) :
    algebraMap R A.homologyZero r = A.homologyAlgebraMap r := sorry

namespace Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- The algebra homomorphism on zeroth homology induced by a chain-DGA homomorphism. -/
noncomputable def homologyZeroMap (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] :
    A.homologyZero →ₐ[R] B.homologyZero :=
  f.homologyHom.degreeZero

/-- The induced map on zeroth homology is Mathlib's canonical homology map in degree zero. -/
@[simp] theorem homologyZeroMap_apply (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] (x : A.homologyZero) :
    f.homologyZeroMap x = f.homologyLinearMap 0 x := sorry

/-- The identity chain-DGA homomorphism induces the identity on zeroth homology algebras. -/
@[simp] theorem homologyZeroMap_id (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    (id A).homologyZeroMap = AlgHom.id R A.homologyZero := sorry

/-- The zeroth-homology algebra map preserves composition of chain-DGA homomorphisms. -/
@[simp] theorem homologyZeroMap_comp (g : Hom B C) (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] [C.IsStrictlyCommutative] :
    (comp g f).homologyZeroMap = g.homologyZeroMap.comp f.homologyZeroMap := sorry

end Hom

end ChainDGAlgebra

namespace ChainDGAlgebra.Strict

variable {R : Type u} [CommRing R]

/-- Canonical zeroth homology is a functor from strictly commutative chain DGAs to commutative
algebras. -/
@[stacks 09PK "zeroth homology functor"]
noncomputable def homologyZero (R : Type u) [CommRing R] :
    ChainDGAlgebra.Strict.{u, v} R ⥤ CommAlgCat.{v} R :=
  homology R ⋙ NonnegGradedAlgebra.degreeZeroFunctor R

/-- The object part of the zeroth-homology functor is the canonical zeroth homology algebra. -/
@[simp] theorem homologyZero_obj (A : ChainDGAlgebra.Strict.{u, v} R) :
    (homologyZero R).obj A =
      CommAlgCat.of R A.toChainDGAlgebra.homologyZero := sorry

/-- The map part of the zeroth-homology functor is the canonical induced algebra map. -/
@[simp] theorem homologyZero_map {A B : ChainDGAlgebra.Strict.{u, v} R} (f : A ⟶ B) :
    (homologyZero R).map f =
      CommAlgCat.ofHom (ChainDGAlgebra.Hom.homologyZeroMap f) := sorry

/-- Evaluation of the zeroth-homology functor is the canonical map on degree-zero homology. -/
@[simp] theorem homologyZero_map_apply {A B : ChainDGAlgebra.Strict.{u, v} R}
    (f : A ⟶ B) (x : A.toChainDGAlgebra.homologyZero) :
    (homologyZero R).map f x = ChainDGAlgebra.Hom.homologyZeroMap f x := sorry

end ChainDGAlgebra.Strict
