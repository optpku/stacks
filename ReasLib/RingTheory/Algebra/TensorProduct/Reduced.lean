/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectivity and Reducedness of Tensor Products

This leaf isolates the elementary tensor-product transports used by geometric
reducedness arguments.  The injectivity statements are formulated over a
commutative base semiring with the exact flat tensor factor required; the
reducedness statements retain that generality, while commutation additionally
requires commutative tensor factors.  The intrinsic geometric-reducedness
predicate and its field-base criteria are owned by
`RingTheory.Nilpotent.GeometricallyReduced.TensorProduct`.
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Tensoring an injective algebra map on the right with a flat left factor is
injective. -/
@[stacks 034N "tensor-product injectivity support"]
theorem map_injective_of_injective_right
    {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R A]
    (f : B →ₐ[R] C) (hf : Function.Injective f) :
    Function.Injective (map (AlgHom.id R A) f) := sorry

/-- Tensoring an injective algebra map on the left with a flat right factor is
injective. -/
@[stacks 034N "tensor-product injectivity support"]
theorem map_injective_of_injective_left
    {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R C]
    (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (map f (AlgHom.id R C)) := sorry

/-- Reducedness descends through an injective map of the left tensor factor when the
right factor is flat over the base. -/
@[stacks 034N "tensor-product reducedness support"]
theorem isReduced_of_injective_left
    {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R C]
    (f : A →ₐ[R] B) (hf : Function.Injective f)
    [IsReduced (B ⊗[R] C)] :
    IsReduced (A ⊗[R] C) := sorry

/-- Explicit-hypothesis form of `isReduced_of_injective_left`; use this bridge when reducedness
of the target tensor product is proposition-valued data rather than an installed instance. -/
@[stacks 034N "explicit reducedness bridge"]
theorem isReduced_of_injective_left_of
    {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R C]
    (f : A →ₐ[R] B) (hf : Function.Injective f)
    (h : IsReduced (B ⊗[R] C)) :
    IsReduced (A ⊗[R] C) := sorry

/-- Reducedness is invariant under the canonical commutativity equivalence of a
commutative algebra tensor product. -/
@[stacks 034N "tensor-product reducedness support"]
theorem isReduced_comm_iff
    {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] :
    IsReduced (A ⊗[R] B) ↔ IsReduced (B ⊗[R] A) := sorry

/-- Tensoring a reduced `k`-algebra on the left with a geometrically reduced
`k`-algebra on the right is reduced. This is an explicit theorem rather than a global instance,
so a consumer chooses the intended tensor-product orientation. -/
@[stacks 034N]
theorem isReduced_of_isGeometricallyReduced_right
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [IsReduced R] [Algebra.IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := sorry

/-- Explicit-hypothesis form of `isReduced_of_isGeometricallyReduced_right`; use this bridge when
the reducedness and geometric-reducedness facts are proposition-valued data rather than installed
instances. -/
@[stacks 034N "explicit geometric-reducedness bridge"]
theorem isReduced_of_isGeometricallyReduced_right_of
    {k : Type u} {R : Type v} {S : Type w}
    [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (hR : IsReduced R) (hS : Algebra.IsGeometricallyReduced k S) :
    IsReduced (R ⊗[k] S) := sorry

end Algebra.TensorProduct
