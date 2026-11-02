/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Distinguished finite free algebras

Commutative associative bilinear multiplications with first basis vector as unit
form a groupoid under unit-fixing linear automorphisms. Ring homomorphisms act
on this groupoid by applying the homomorphism to structure constants and matrices.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace FreeDimAlgebra

private structure Object (R : Type u) [CommRing R] (d : ℕ) [NeZero d] where
  multiplication : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R)
  associative : ∀ x y z, multiplication (multiplication x y) z = multiplication x (multiplication y z)
  commutative : ∀ x y, multiplication x y = multiplication y x
  unital : ∀ x, multiplication (Pi.single 0 1) x = x

private structure Arrow {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m m' : Object R d) where
  automorphism : LinearMap.GeneralLinearGroup R (Fin d → R)
  fixesUnit : automorphism.val (Pi.single 0 1) = Pi.single 0 1
  intertwines : ∀ x y, m.multiplication (automorphism.val x) (automorphism.val y) =
    automorphism.val (m'.multiplication x y)

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

namespace Object

/-- A bilinear multiplication that is associative, commutative, and has first basis
vector as unit determines a distinguished algebra structure. -/
private def ofMul (mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (mul_comm : ∀ x y, mul x y = mul y x)
    (one_mul : ∀ x, mul (Pi.single 0 1) x = x) : Object R d :=
  ⟨mul, mul_assoc, mul_comm, one_mul⟩

end Object

namespace Arrow

/-- An invertible linear map fixing the first basis vector and intertwining two
multiplications determines a contravariant algebra arrow. -/
private def of {m m' : Object R d} (e : LinearMap.GeneralLinearGroup R (Fin d → R))
    (map_one : e.val (Pi.single 0 1) = Pi.single 0 1)
    (map_mul : ∀ x y, m.multiplication (e.val x) (e.val y) =
      e.val (m'.multiplication x y)) : Arrow m m' :=
  ⟨e, map_one, map_mul⟩

end Arrow

private theorem id_laws (m : Object R d) :
    (1 : LinearMap.GeneralLinearGroup R (Fin d → R)).val (Pi.single 0 1) = Pi.single 0 1 ∧
    (∀ x y, m.multiplication ((1 : LinearMap.GeneralLinearGroup R (Fin d → R)).val x)
      ((1 : LinearMap.GeneralLinearGroup R (Fin d → R)).val y) =
      (1 : LinearMap.GeneralLinearGroup R (Fin d → R)).val (m.multiplication x y)) :=
  ⟨rfl, fun _ _ ↦ rfl⟩

private def arrowId (m : Object R d) : Arrow m m :=
  Arrow.of 1 (id_laws m).1 (id_laws m).2

private theorem comp_laws {m₁ m₂ m₃ : Object R d} (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) :
    (f.automorphism * g.automorphism).val (Pi.single 0 1) = Pi.single 0 1 ∧
    (∀ x y, m₁.multiplication ((f.automorphism * g.automorphism).val x)
      ((f.automorphism * g.automorphism).val y) =
      (f.automorphism * g.automorphism).val (m₃.multiplication x y)) := by
  constructor
  · change f.automorphism.val (g.automorphism.val (Pi.single 0 1)) = Pi.single 0 1
    rw [g.fixesUnit, f.fixesUnit]
  · intro x y
    change m₁.multiplication (f.automorphism.val (g.automorphism.val x))
      (f.automorphism.val (g.automorphism.val y)) =
        f.automorphism.val (g.automorphism.val (m₃.multiplication x y))
    rw [f.intertwines, g.intertwines]

private def arrowComp {m₁ m₂ m₃ : Object R d} (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) :
    Arrow m₁ m₃ :=
  Arrow.of (f.automorphism * g.automorphism) (comp_laws f g).1 (comp_laws f g).2

private theorem inv_laws {m m' : Object R d} (f : Arrow m m') :
    f.automorphism⁻¹.val (Pi.single 0 1) = Pi.single 0 1 ∧
    (∀ x y, m'.multiplication (f.automorphism⁻¹.val x) (f.automorphism⁻¹.val y) =
      f.automorphism⁻¹.val (m.multiplication x y)) := by
  have hinv (x : Fin d → R) : f.automorphism.val (f.automorphism⁻¹.val x) = x :=
    f.automorphism.toLinearEquiv.apply_symm_apply x
  constructor
  · apply f.automorphism.toLinearEquiv.injective
    change f.automorphism.val (f.automorphism⁻¹.val (Pi.single 0 1)) =
      f.automorphism.val (Pi.single 0 1)
    rw [hinv, f.fixesUnit]
  · intro x y
    apply f.automorphism.toLinearEquiv.injective
    change f.automorphism.val
      (m'.multiplication (f.automorphism⁻¹.val x) (f.automorphism⁻¹.val y)) =
        f.automorphism.val (f.automorphism⁻¹.val (m.multiplication x y))
    rw [← f.intertwines, hinv, hinv, hinv]

private def arrowInv {m m' : Object R d} (f : Arrow m m') : Arrow m' m :=
  Arrow.of f.automorphism⁻¹ (inv_laws f).1 (inv_laws f).2

private theorem Arrow.ext {m m' : Object R d} {f g : Arrow m m'}
    (h : f.automorphism = g.automorphism) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem groupoid_laws (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp (arrowId m) f = f) ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp f (arrowId m') = f) ∧
    (∀ (m₁ m₂ m₃ m₄ : Object R d) (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) (h : Arrow m₃ m₄),
      arrowComp (arrowComp f g) h = arrowComp f (arrowComp g h)) ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp (arrowInv f) f = arrowId m') ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp f (arrowInv f) = arrowId m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m m' f
    apply Arrow.ext
    exact one_mul f.automorphism
  · intro m m' f
    apply Arrow.ext
    exact mul_one f.automorphism
  · intro m₁ m₂ m₃ m₄ f g h
    apply Arrow.ext
    exact mul_assoc f.automorphism g.automorphism h.automorphism
  · intro m m' f
    apply Arrow.ext
    exact inv_mul_cancel f.automorphism
  · intro m m' f
    apply Arrow.ext
    exact mul_inv_cancel f.automorphism

@[implicit_reducible] private def objectGroupoid (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    Groupoid (Object R d) where
  Hom := Arrow
  id := arrowId
  comp := arrowComp
  id_comp := (groupoid_laws R d).1 _ _
  comp_id := (groupoid_laws R d).2.1 _ _
  assoc := (groupoid_laws R d).2.2.1 _ _ _ _
  inv := arrowInv
  inv_comp := (groupoid_laws R d).2.2.2.1 _ _
  comp_inv := (groupoid_laws R d).2.2.2.2 _ _

end FreeDimAlgebra

/-- The groupoid of commutative associative algebra structures on `Fin d → R`
with first basis vector as unit and unit-fixing contravariant linear intertwiners. -/
@[implicit_reducible] def FreeDimAlgebra (R : Type u) [CommRing R] (d : ℕ) [NeZero d] : Grpd.{u, u} :=
  ⟨FreeDimAlgebra.Object R d, FreeDimAlgebra.objectGroupoid R d⟩

namespace FreeDimAlgebra

/-- The unit vector `e₁ = (1, 0, …, 0)` of `Fin d → R`. -/
def one (R : Type u) [CommRing R] (d : ℕ) [NeZero d] : Fin d → R :=
  Pi.single 0 1

/-- The unit vector is the first standard basis vector. -/
theorem one_eq (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    one R d = Pi.single 0 1 := rfl

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

/-- The bilinear multiplication of a distinguished algebra structure. -/
def mul (m : FreeDimAlgebra R d) :
    (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R) := m.multiplication

/-- Distinguished algebra structures are determined by their multiplications. -/
theorem object_ext {m n : FreeDimAlgebra R d} (h : mul m = mul n) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The multiplication of a distinguished algebra structure is associative. -/
theorem mul_assoc (m : FreeDimAlgebra R d) (x y z : Fin d → R) :
    mul m (mul m x y) z = mul m x (mul m y z) := m.associative x y z

/-- The multiplication of a distinguished algebra structure is commutative. -/
theorem mul_comm (m : FreeDimAlgebra R d) (x y : Fin d → R) :
    mul m x y = mul m y x := m.commutative x y

/-- The first basis vector is a left unit for a distinguished algebra structure. -/
theorem one_mul (m : FreeDimAlgebra R d) (x : Fin d → R) :
    mul m (one R d) x = x := m.unital x

namespace Object
export FreeDimAlgebra (mul mul_assoc mul_comm one_mul)
end Object

/-- Assemble a distinguished algebra from a bilinear multiplication and its laws. -/
def ofMul (mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (mul_comm : ∀ x y, mul x y = mul y x)
    (one_mul : ∀ x, mul (one R d) x = x) : FreeDimAlgebra R d :=
  Object.ofMul mul mul_assoc mul_comm one_mul

/-- The multiplication of `ofMul mul …` is the supplied bilinear map. -/
theorem ofMul_mul (mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (mul_comm : ∀ x y, mul x y = mul y x)
    (one_mul : ∀ x, mul (one R d) x = x) :
    (ofMul mul mul_assoc mul_comm one_mul).mul = mul := rfl

/-- A distinguished algebra is unital, commutative, and associative. -/
theorem spec (m : FreeDimAlgebra R d) :
    (∀ x, m.mul (one R d) x = x) ∧
      (∀ x y, m.mul x y = m.mul y x) ∧
        (∀ x y z, m.mul (m.mul x y) z = m.mul x (m.mul y z)) :=
  ⟨one_mul m, mul_comm m, mul_assoc m⟩

/-- The unit vector is also a right unit. -/
theorem mul_one (m : FreeDimAlgebra R d) (x : Fin d → R) :
    m.mul x (one R d) = x := by
  rw [mul_comm, one_mul]

/-- The coordinates of multiplication on pairs of standard basis vectors. -/
def structureConst (m : FreeDimAlgebra R d) (i j k : Fin d) : R :=
  m.mul (Pi.single i 1) (Pi.single j 1) k

/-- Reconstruct bilinear multiplication from structure constants using the standard basis. -/
def mulOfStructureConst (a : Fin d → Fin d → Fin d → R) :
    (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R) :=
  let b := Pi.basisFun R (Fin d)
  b.constr R fun i ↦ b.constr R fun j ↦ fun k ↦ a i j k

/-- Evaluation on pairs of standard basis vectors recovers the structure constants. -/
theorem mulOfStructureConst_structureConst (a : Fin d → Fin d → Fin d → R)
    (i j k : Fin d) :
    mulOfStructureConst a (Pi.single i 1) (Pi.single j 1) k = a i j k := by
  rw [← Pi.basisFun_apply R (Fin d) i, ← Pi.basisFun_apply R (Fin d) j]
  simp only [mulOfStructureConst, Module.Basis.constr_basis]

/-- The arrows between distinguished algebra structures in their bundled groupoid. -/
abbrev Hom (m m' : FreeDimAlgebra R d) := m ⟶ m'

namespace Hom

/-- The invertible linear map underlying an algebra arrow. -/
def equiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    LinearMap.GeneralLinearGroup R (Fin d → R) := f.automorphism

/-- Algebra arrows are determined by their underlying linear automorphisms. -/
theorem ext {m m' : FreeDimAlgebra R d} {f g : Hom m m'}
    (h : f.equiv = g.equiv) : f = g := Arrow.ext h

/-- An algebra arrow fixes the distinguished unit. -/
theorem map_one {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (equiv f).val (one R d) = one R d := f.fixesUnit

/-- An algebra arrow intertwines the source and target multiplications contravariantly. -/
theorem map_mul {m m' : FreeDimAlgebra R d} (f : Hom m m') (x y : Fin d → R) :
    m.mul ((equiv f).val x) ((equiv f).val y) = (equiv f).val (m'.mul x y) :=
  f.intertwines x y

end Hom

namespace Arrow
export Hom (equiv map_one map_mul)
end Arrow

namespace Hom

/-- Assemble an algebra arrow from an invertible linear map and its unit and multiplication laws. -/
def of {m m' : FreeDimAlgebra R d} (e : LinearMap.GeneralLinearGroup R (Fin d → R))
    (map_one : e.val (one R d) = one R d)
    (map_mul : ∀ x y, m.mul (e.val x) (e.val y) = e.val (m'.mul x y)) : Hom m m' :=
  Arrow.of e map_one map_mul

/-- The identity arrow of a distinguished algebra structure. -/
def id (m : FreeDimAlgebra R d) : Hom m m := arrowId m

/-- The underlying linear automorphism of the identity arrow is the identity. -/
theorem id_equiv (m : FreeDimAlgebra R d) : (id m).equiv = 1 := rfl

/-- Composition of algebra arrows, with underlying automorphism `f.equiv * g.equiv`. -/
def comp {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    Hom m₁ m₃ := arrowComp f g

/-- The underlying linear automorphism of a composite is the product of the automorphisms. -/
theorem comp_equiv {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    (comp f g).equiv = f.equiv * g.equiv := rfl

/-- The inverse algebra arrow, given by the inverse linear automorphism. -/
def inv {m m' : FreeDimAlgebra R d} (f : Hom m m') : Hom m' m := arrowInv f

/-- The underlying linear automorphism of an inverse arrow is the inverse automorphism. -/
theorem inv_equiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (inv f).equiv = f.equiv⁻¹ := rfl

/-- The linear equivalence underlying an algebra arrow. -/
def toLinearEquiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (Fin d → R) ≃ₗ[R] (Fin d → R) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv f.equiv

/-- The matrix in `GL_d(R)` associated to an algebra arrow. -/
def toGL {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    Matrix.GeneralLinearGroup (Fin d) R :=
  Matrix.GeneralLinearGroup.toLin.symm f.equiv

/-- An algebra arrow fixes the unit and intertwines multiplications. -/
theorem spec {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    f.equiv.val (one R d) = one R d ∧
      ∀ x y, m.mul (f.equiv.val x) (f.equiv.val y) = f.equiv.val (m'.mul x y) :=
  ⟨map_one f, map_mul f⟩

end Hom

omit [NeZero d] in
private theorem linear_apply_eq_sum (g : (Fin d → R) →ₗ[R] (Fin d → R))
    (x : Fin d → R) (k : Fin d) :
    g x k = ∑ i : Fin d, x i * g (Pi.single i 1) k := by
  simpa using
    (congrArg (fun v ↦ g v k) ((Pi.basisFun R (Fin d)).sum_repr x)).symm

omit [NeZero d] in
private theorem bilinear_apply_eq_sum
    (b : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (x y : Fin d → R) (k : Fin d) :
    b x y k = ∑ i : Fin d, ∑ j : Fin d,
      x i * y j * b (Pi.single i 1) (Pi.single j 1) k := by
  rw [show b x y k = b.flip y x k from rfl, linear_apply_eq_sum]
  simp only [LinearMap.flip_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [linear_apply_eq_sum (b (Pi.single i 1)) y k, Finset.mul_sum]
  simp only [_root_.mul_assoc]

omit [NeZero d] in
private theorem map_single {S : Type u} [CommRing S] (f : R →+* S) (i : Fin d) :
    (fun k ↦ f ((Pi.single i 1 : Fin d → R) k)) = (Pi.single i 1 : Fin d → S) := by
  funext k
  by_cases h : i = k <;> simp [Pi.single_apply, h]

private theorem mulOfStructureConst_map {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) (x y : Fin d → R) :
    mulOfStructureConst (fun i j k ↦ f (structureConst m i j k))
      (fun i ↦ f (x i)) (fun i ↦ f (y i)) = fun k ↦ f (m.mul x y k) := by
  funext k
  rw [bilinear_apply_eq_sum _ _ _ k, bilinear_apply_eq_sum m.mul x y k]
  simp only [mulOfStructureConst_structureConst, structureConst, map_sum, _root_.map_mul]

private theorem baseChange_laws {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) :
    let b := mulOfStructureConst (fun i j k ↦ f (structureConst m i j k))
    (∀ x y z, b (b x y) z = b x (b y z)) ∧
    (∀ x y, b x y = b y x) ∧ (∀ x, b (one S d) x = x) := by
  let b := mulOfStructureConst (fun i j k ↦ f (structureConst m i j k))
  have hmap (x y : Fin d → R) :
      b (fun i ↦ f (x i)) (fun i ↦ f (y i)) = fun k ↦ f (m.mul x y k) :=
    mulOfStructureConst_map f m x y
  refine ⟨?_, ?_, ?_⟩
  · have h :
        (LinearMap.llcomp S (Fin d → S) (Fin d → S)
          ((Fin d → S) →ₗ[S] (Fin d → S)) b).comp b =
        (LinearMap.llcomp S (Fin d → S) (Fin d → S) (Fin d → S)).compl₁₂ b b := by
      apply (Pi.basisFun S (Fin d)).ext
      intro i
      apply (Pi.basisFun S (Fin d)).ext
      intro j
      apply (Pi.basisFun S (Fin d)).ext
      intro k
      change b (b ((Pi.basisFun S (Fin d)) i) ((Pi.basisFun S (Fin d)) j))
        ((Pi.basisFun S (Fin d)) k) =
          b ((Pi.basisFun S (Fin d)) i)
            (b ((Pi.basisFun S (Fin d)) j) ((Pi.basisFun S (Fin d)) k))
      simp only [Pi.basisFun_apply, ← map_single f, hmap]
      exact congrArg (fun v : Fin d → R ↦ fun n ↦ f (v n))
        (mul_assoc m (Pi.single i 1) (Pi.single j 1) (Pi.single k 1))
    intro x y z
    exact congrArg (fun c ↦ c x y z) h
  · have h : b = b.flip := by
      apply (Pi.basisFun S (Fin d)).ext
      intro i
      apply (Pi.basisFun S (Fin d)).ext
      intro j
      change b ((Pi.basisFun S (Fin d)) i) ((Pi.basisFun S (Fin d)) j) =
        b ((Pi.basisFun S (Fin d)) j) ((Pi.basisFun S (Fin d)) i)
      simp only [Pi.basisFun_apply, ← map_single f, hmap]
      exact congrArg (fun v : Fin d → R ↦ fun k ↦ f (v k))
        (mul_comm m (Pi.single i 1) (Pi.single j 1))
    intro x y
    exact congrArg (fun c ↦ c x y) h
  · have h : b (one S d) = LinearMap.id := by
      apply (Pi.basisFun S (Fin d)).ext
      intro i
      change b (one S d) ((Pi.basisFun S (Fin d)) i) = (Pi.basisFun S (Fin d)) i
      simp only [one, Pi.basisFun_apply, ← map_single f, hmap]
      exact congrArg (fun v : Fin d → R ↦ fun k ↦ f (v k)) (one_mul m (Pi.single i 1))
    intro x
    exact congrArg (fun c ↦ c x) h

/-- Base change applies a ring homomorphism to the structure constants of multiplication. -/
def baseChange {S : Type u} [CommRing S] (f : R →+* S) (m : FreeDimAlgebra R d) :
    FreeDimAlgebra S d :=
  ofMul (mulOfStructureConst (fun i j k ↦ f (structureConst m i j k)))
    (baseChange_laws f m).1 (baseChange_laws f m).2.1 (baseChange_laws f m).2.2

/-- The structure constants after base change are the images of the original constants. -/
theorem baseChange_structureConst {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) (i j k : Fin d) :
    structureConst (baseChange f m) i j k = f (structureConst m i j k) :=
  mulOfStructureConst_structureConst _ i j k

namespace Hom

private theorem baseChange_laws {S : Type u} [CommRing S] (f : R →+* S)
    {m m' : FreeDimAlgebra R d} (φ : Hom m m') :
    let e := Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm φ.equiv))
    e.val (one S d) = one S d ∧
    (∀ x y, (FreeDimAlgebra.baseChange f m).mul (e.val x) (e.val y) =
      e.val ((FreeDimAlgebra.baseChange f m').mul x y)) := by
  let A := Matrix.GeneralLinearGroup.toLin.symm φ.equiv
  let e := Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map f A)
  have he (x : Fin d → R) :
      e.val (fun i ↦ f (x i)) = fun k ↦ f (φ.equiv.val x k) := by
    calc
      e.val (fun i ↦ f (x i)) =
          fun k ↦ f ((Matrix.GeneralLinearGroup.toLin A).val x k) := by
        funext k
        change (Matrix.GeneralLinearGroup.map f A).val.mulVec (fun i ↦ f (x i)) k =
          f (A.val.mulVec x k)
        simp only [Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map_apply,
          map_sum, _root_.map_mul]
      _ = fun k ↦ f (φ.equiv.val x k) := by
        simp only [A, MulEquiv.apply_symm_apply]
  have hm (a : FreeDimAlgebra R d) (x y : Fin d → R) :
      (FreeDimAlgebra.baseChange f a).mul (fun i ↦ f (x i)) (fun i ↦ f (y i)) =
        fun k ↦ f (a.mul x y k) := mulOfStructureConst_map f a x y
  constructor
  · change e.val (one S d) = one S d
    calc
      e.val (one S d) = e.val (fun i ↦ f (one R d i)) :=
        congrArg e.val (map_single f 0).symm
      _ = fun k ↦ f (φ.equiv.val (one R d) k) := he _
      _ = fun k ↦ f (one R d k) :=
        congrArg (fun v : Fin d → R ↦ fun k ↦ f (v k)) (map_one φ)
      _ = one S d := map_single f 0
  · have h :
        (FreeDimAlgebra.baseChange f m).mul.compl₁₂ e.val e.val =
        (FreeDimAlgebra.baseChange f m').mul.compr₂ e.val := by
      apply (Pi.basisFun S (Fin d)).ext
      intro i
      apply (Pi.basisFun S (Fin d)).ext
      intro j
      change (FreeDimAlgebra.baseChange f m).mul
        (e.val ((Pi.basisFun S (Fin d)) i)) (e.val ((Pi.basisFun S (Fin d)) j)) =
          e.val ((FreeDimAlgebra.baseChange f m').mul
            ((Pi.basisFun S (Fin d)) i) ((Pi.basisFun S (Fin d)) j))
      simp only [Pi.basisFun_apply, ← map_single f, he, hm]
      exact congrArg (fun v : Fin d → R ↦ fun k ↦ f (v k))
        (map_mul φ (Pi.single i 1) (Pi.single j 1))
    intro x y
    exact congrArg (fun c ↦ c x y) h

/-- Base change of an algebra arrow applies the ring homomorphism to its matrix entries. -/
def baseChange {S : Type u} [CommRing S] (f : R →+* S) {m m' : FreeDimAlgebra R d}
    (φ : Hom m m') : Hom (FreeDimAlgebra.baseChange f m) (FreeDimAlgebra.baseChange f m') :=
  of (Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm φ.equiv)))
    (baseChange_laws f φ).1 (baseChange_laws f φ).2

end Hom

/-- The groupoid structure stored in the distinguished algebra groupoid. -/
@[implicit_reducible] def groupoid (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    Groupoid (FreeDimAlgebra R d) := (FreeDimAlgebra R d).str

private theorem baseChangeFunctor_laws {S : Type u} [CommRing S] (f : R →+* S) :
    (∀ m : FreeDimAlgebra R d, Hom.baseChange f (𝟙 m) = 𝟙 (baseChange f m)) ∧
    (∀ (m₁ m₂ m₃ : FreeDimAlgebra R d) (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃),
      Hom.baseChange f (φ ≫ ψ) = Hom.baseChange f φ ≫ Hom.baseChange f ψ) := by
  constructor
  · intro m
    apply Arrow.ext
    change Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm 1)) = 1
    simp
  · intro m₁ m₂ m₃ φ ψ
    apply Arrow.ext
    change Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f
        (Matrix.GeneralLinearGroup.toLin.symm (φ.automorphism * ψ.automorphism))) =
      Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm φ.automorphism)) *
      Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm ψ.automorphism))
    simp only [map_mul]

/-- The functorial action of a ring homomorphism on distinguished algebra groupoids. -/
def baseChangeFunctor {S : Type u} [CommRing S] (f : R →+* S) :
    FreeDimAlgebra R d ⥤ FreeDimAlgebra S d where
  obj := baseChange f
  map φ := Hom.baseChange f φ
  map_id := (baseChangeFunctor_laws f).1
  map_comp := (baseChangeFunctor_laws f).2 _ _ _

/-- On objects, the base change functor applies base change to multiplication. -/
theorem baseChangeFunctor_obj {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) :
    (baseChangeFunctor f).obj m = baseChange f m := rfl

/-- Base change along the identity ring homomorphism is the identity functor. -/
theorem baseChangeFunctor_id (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    baseChangeFunctor (d := d) (RingHom.id R) = 𝟭 (FreeDimAlgebra R d) := by
  sorry

/-- Base change along a composite is the composite of the base change functors. -/
theorem baseChangeFunctor_comp {S T : Type u} [CommRing S] [CommRing T]
    (d : ℕ) [NeZero d] (f : R →+* S) (g : S →+* T) :
    baseChangeFunctor (d := d) (g.comp f) =
      baseChangeFunctor (d := d) f ⋙ baseChangeFunctor (d := d) g := by
  sorry

end FreeDimAlgebra
end AlgebraicGeometry
