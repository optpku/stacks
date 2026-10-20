/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Solution
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne

/-!
# Square-zero algebra extensions with specified coefficients

Geometric square-zero extensions determine classes in the cotangent cokernel.
Conversely, a conormal map is realized by its graph-ideal pushout.
-/

@[expose] public section
noncomputable section
universe u
open Algebra Algebra.Generators Algebra.Extension TrivSqZeroExt
namespace Algebra
variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- A geometric square-zero `A`-algebra extension `0 → N → C → B → 0`. -/
structure SquareZeroAlgExtension where
  /-- The middle ring of the extension. -/
  carrier : Type u
  /-- Commutative ring structure on the middle term. -/
  [commRing : CommRing carrier]
  /-- The structure map `A → carrier`. -/
  [algebra : Algebra A carrier]
  /-- The square-zero surjection onto `B`. -/
  toB : carrier →ₐ[A] B
  /-- The projection is a square-zero extension. -/
  [isSquareZero : toB.toRingHom.IsSquareZeroExtension]
  /-- `B`-linear identification of the conormal of the kernel with `N`. -/
  kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N

namespace SquareZeroAlgExtension

variable {A B N}

/-- Assemble a square-zero algebra extension from a middle ring, a square-zero
surjection onto `B`, and a kernel identification. -/
def of {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [hsq : toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    SquareZeroAlgExtension A B N where
  carrier := C
  commRing := inferInstance
  algebra := inferInstance
  toB := toB
  isSquareZero := hsq
  kernelEquiv := kernelEquiv

/-- The middle ring of `of` is the supplied carrier. -/
theorem of_carrier {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    (of toB kernelEquiv).carrier = C := rfl

/-- The projection of `of` is the supplied algebra map. -/
theorem of_toB {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    (of toB kernelEquiv).toB = toB := rfl

private theorem toHomValue_mem (e : SquareZeroAlgExtension A B N)
    (x : (Generators.self A B).toExtension.Cotangent) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let liftGen : B → e.carrier := Function.surjInv e.isSquareZero.surjective
  let φ : (Generators.self A B).toExtension.Ring →ₐ[A] e.carrier := MvPolynomial.aeval liftGen
  let y := Function.surjInv Cotangent.mk_surjective x
  φ y.1 ∈ RingHom.ker e.toB.toRingHom := sorry

private def toHomValue (e : SquareZeroAlgExtension A B N)
    (x : (Generators.self A B).toExtension.Cotangent) : N :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let liftGen : B → e.carrier := Function.surjInv e.isSquareZero.surjective
  let φ : (Generators.self A B).toExtension.Ring →ₐ[A] e.carrier := MvPolynomial.aeval liftGen
  let y := Function.surjInv Cotangent.mk_surjective x
  e.kernelEquiv (Ideal.toCotangent _ ⟨φ y.1, toHomValue_mem e x⟩)

private theorem toHomValue_add (e : SquareZeroAlgExtension A B N)
    (x y : (Generators.self A B).toExtension.Cotangent) :
    toHomValue e (x + y) = toHomValue e x + toHomValue e y := sorry

private theorem toHomValue_smul (e : SquareZeroAlgExtension A B N)
    (r : B) (x : (Generators.self A B).toExtension.Cotangent) :
    toHomValue e (r • x) = r • toHomValue e x := sorry

/-- A geometric extension determines a linear map from the self-presentation conormal module. -/
def toHom (e : SquareZeroAlgExtension A B N) :
    (Generators.self A B).toExtension.Cotangent →ₗ[B] N :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  { toFun := fun x =>
      let liftGen : B → e.carrier := Function.surjInv e.isSquareZero.surjective
      let φ : (Generators.self A B).toExtension.Ring →ₐ[A] e.carrier := MvPolynomial.aeval liftGen
      let y := Function.surjInv Cotangent.mk_surjective x
      e.kernelEquiv (Ideal.toCotangent _ ⟨φ y.1, by exact toHomValue_mem e x⟩)
    map_add' := by exact toHomValue_add e
    map_smul' := by exact toHomValue_smul e }

/-- The cotangent cokernel class determined by a geometric extension. -/
def toClass (e : SquareZeroAlgExtension A B N) : Exal A B N :=
  Exal.mk A B N (toHom e)

private def ofHomGraph (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Set (TrivSqZeroExt (Generators.self A B).toExtension.Ring N) :=
  Set.range fun x : (Generators.self A B).toExtension.ker ↦
    (inl x.1 : TrivSqZeroExt (Generators.self A B).toExtension.Ring N) -
      inr (f (Cotangent.mk x))

private theorem mem_ofHomGraph (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (z : TrivSqZeroExt (Generators.self A B).toExtension.Ring N) :
    z ∈ ofHomGraph f ↔ ∃ x : (Generators.self A B).toExtension.ker,
      z = inl x.1 - inr (f (Cotangent.mk x)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

private theorem ofHom_toB_kills (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  ∀ z, z ∈ Ideal.span (ofHomGraph f) → ((IsScalarTower.toAlgHom A P.Ring B).comp (fstHom A P.Ring N)).toRingHom z = 0 := sorry

private def ofHomProjectionRing (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  (TrivSqZeroExt P.Ring N ⧸ Ideal.span (ofHomGraph f)) →+* B :=
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  Ideal.Quotient.lift (Ideal.span (ofHomGraph f)) ((IsScalarTower.toAlgHom A P.Ring B).comp (fstHom A P.Ring N)).toRingHom (ofHom_toB_kills f)

private theorem ofHom_toB_commutes (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  ∀ a : A, ofHomProjectionRing f (algebraMap A (TrivSqZeroExt P.Ring N ⧸ Ideal.span (ofHomGraph f)) a) = algebraMap A B a := sorry

private def ofHomProjection (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  (TrivSqZeroExt P.Ring N ⧸ Ideal.span (ofHomGraph f)) →ₐ[A] B :=
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  { toRingHom := ofHomProjectionRing f
    commutes' := ofHom_toB_commutes f }

private theorem ofHom_toB_isSquareZero (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  (ofHomProjection f).toRingHom.IsSquareZeroExtension := sorry

private theorem ofHom_kernelValue_mem (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  ∀ (z : TrivSqZeroExt P.Ring N), ofHomProjection f (Quotient.mk _ z) = 0 →
    TrivSqZeroExt.fst z ∈ P.ker := sorry

private theorem ofHom_kernelValue_wellDefined (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  ∀ (z w : TrivSqZeroExt P.Ring N),
    (Ideal.span (ofHomGraph f)).quotientRel z w → HEq ((fun z (hz : ofHomProjection f (Quotient.mk _ z) = 0) ↦
    TrivSqZeroExt.snd z + f (Cotangent.mk ⟨TrivSqZeroExt.fst z, ofHom_kernelValue_mem f z hz⟩)) z) ((fun z (hz : ofHomProjection f (Quotient.mk _ z) = 0) ↦
    TrivSqZeroExt.snd z + f (Cotangent.mk ⟨TrivSqZeroExt.fst z, ofHom_kernelValue_mem f z hz⟩)) w) := sorry

private def ofHomKernelValue (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI := ofHom_toB_isSquareZero f
  Ideal.Cotangent (RingHom.ker (ofHomProjection f).toRingHom) → N :=
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI := ofHom_toB_isSquareZero f
  fun x ↦
    let y := (RingHom.SquareZeroExtension.toCotangentEquiv_source
      (ofHomProjection f).toRingHom).symm x
    Quotient.hrecOn y.1 (fun z (hz : ofHomProjection f (Quotient.mk _ z) = 0) ↦
    TrivSqZeroExt.snd z + f (Cotangent.mk ⟨TrivSqZeroExt.fst z, ofHom_kernelValue_mem f z hz⟩)) (ofHom_kernelValue_wellDefined f) y.2

private theorem ofHom_kernelValue_add (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI := ofHom_toB_isSquareZero f
  ∀ x y, ofHomKernelValue f (x + y) = ofHomKernelValue f x + ofHomKernelValue f y := sorry

private theorem ofHom_kernelValue_smul (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI := ofHom_toB_isSquareZero f
  ∀ (r : B) x, ofHomKernelValue f (r • x) = r • ofHomKernelValue f x := sorry

private theorem ofHom_kernelValue_bijective (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI := ofHom_toB_isSquareZero f
  Function.Bijective (ofHomKernelValue f) := sorry

/-- The graph-ideal quotient realizes a conormal map as a square-zero algebra extension. -/
def ofHom (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) : SquareZeroAlgExtension A B N :=
  let P := (Generators.self A B).toExtension
  -- Local instance justification (noncanonical choice): the presentation map selects the action on N.
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  -- Local instance justification (instance diamond): choose the opposite action only for this graph quotient.
  letI : Module P.Ringᵐᵒᵖ N :=
    Module.compHom N ((RingHom.id P.Ring).fromOpposite fun x y ↦ mul_comm x y)
  -- Local instance justification (instance diamond): centrality belongs to the selected opposite action.
  letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  -- Local instance justification (noncanonical choice): restrict the chosen presentation action to the base.
  letI : Module A N := Module.compHom N (algebraMap A P.Ring)
  -- Local instance justification (proof-local temporary data): the graph algebra uses this scalar tower.
  letI : IsScalarTower A P.Ring N := ⟨fun a r n ↦ by
    change (a • r) • n = (algebraMap A P.Ring a) • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (proof-local temporary data): the graph algebra also uses the opposite scalar tower.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun a r n ↦ by
    change (a • r.unop) • n = (algebraMap A P.Ring a) • (r.unop • n)
    rw [Algebra.smul_def, mul_smul]⟩
  -- Local instance justification (instance diamond): the two selected presentation actions commute.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun r t n ↦ by
    change r • (t.unop • n) = t.unop • (r • n)
    rw [← mul_smul, mul_comm, mul_smul]⟩
  let I := Ideal.span (Set.range fun x : P.ker ↦
    (inl x.1 : TrivSqZeroExt P.Ring N) - inr (f (Cotangent.mk x)))
  let toB : (TrivSqZeroExt P.Ring N ⧸ I) →ₐ[A] B :=
    { toRingHom :=
      Ideal.Quotient.lift I ((IsScalarTower.toAlgHom A P.Ring B).comp (fstHom A P.Ring N)).toRingHom (by exact ofHom_toB_kills f)
      commutes' := by exact ofHom_toB_commutes f }
  -- Local instance justification (proof-local temporary data): the graph projection is square-zero.
  letI : toB.toRingHom.IsSquareZeroExtension := by exact ofHom_toB_isSquareZero f
  of toB (LinearEquiv.ofBijective
    { toFun := fun x ↦
        let y := (RingHom.SquareZeroExtension.toCotangentEquiv_source toB.toRingHom).symm x
        Quotient.hrecOn y.1
          (fun z (hz : toB (Quotient.mk _ z) = 0) ↦
            TrivSqZeroExt.snd z + f (Cotangent.mk
              ⟨TrivSqZeroExt.fst z, by exact ofHom_kernelValue_mem f z hz⟩))
          (by exact ofHom_kernelValue_wellDefined f) y.2
      map_add' := by exact ofHom_kernelValue_add f
      map_smul' := by exact ofHom_kernelValue_smul f }
    (by exact ofHom_kernelValue_bijective f))

/-- The graph-ideal realization has the extension class of its defining conormal map. -/
theorem toClass_ofHom (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    toClass (ofHom f) = Exal.mk A B N f := sorry

end SquareZeroAlgExtension
end Algebra
