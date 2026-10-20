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
      (1 : LinearMap.GeneralLinearGroup R (Fin d → R)).val (m.multiplication x y)) := sorry

private def arrowId (m : Object R d) : Arrow m m :=
  Arrow.of 1 (id_laws m).1 (id_laws m).2

private theorem comp_laws {m₁ m₂ m₃ : Object R d} (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) :
    (f.automorphism * g.automorphism).val (Pi.single 0 1) = Pi.single 0 1 ∧
    (∀ x y, m₁.multiplication ((f.automorphism * g.automorphism).val x)
      ((f.automorphism * g.automorphism).val y) =
      (f.automorphism * g.automorphism).val (m₃.multiplication x y)) := sorry

private def arrowComp {m₁ m₂ m₃ : Object R d} (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) :
    Arrow m₁ m₃ :=
  Arrow.of (f.automorphism * g.automorphism) (comp_laws f g).1 (comp_laws f g).2

private theorem inv_laws {m m' : Object R d} (f : Arrow m m') :
    f.automorphism⁻¹.val (Pi.single 0 1) = Pi.single 0 1 ∧
    (∀ x y, m'.multiplication (f.automorphism⁻¹.val x) (f.automorphism⁻¹.val y) =
      f.automorphism⁻¹.val (m.multiplication x y)) := sorry

private def arrowInv {m m' : Object R d} (f : Arrow m m') : Arrow m' m :=
  Arrow.of f.automorphism⁻¹ (inv_laws f).1 (inv_laws f).2

private theorem groupoid_laws (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp (arrowId m) f = f) ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp f (arrowId m') = f) ∧
    (∀ (m₁ m₂ m₃ m₄ : Object R d) (f : Arrow m₁ m₂) (g : Arrow m₂ m₃) (h : Arrow m₃ m₄),
      arrowComp (arrowComp f g) h = arrowComp f (arrowComp g h)) ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp (arrowInv f) f = arrowId m') ∧
    (∀ (m m' : Object R d) (f : Arrow m m'), arrowComp f (arrowInv f) = arrowId m) := sorry

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
    one R d = Pi.single 0 1 := sorry

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

/-- The bilinear multiplication of a distinguished algebra structure. -/
def mul (m : FreeDimAlgebra R d) :
    (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R) := m.multiplication

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
    (ofMul mul mul_assoc mul_comm one_mul).mul = mul := sorry

/-- A distinguished algebra is unital, commutative, and associative. -/
theorem spec (m : FreeDimAlgebra R d) :
    (∀ x, m.mul (one R d) x = x) ∧
      (∀ x y, m.mul x y = m.mul y x) ∧
        (∀ x y z, m.mul (m.mul x y) z = m.mul x (m.mul y z)) := sorry

/-- The unit vector is also a right unit. -/
theorem mul_one (m : FreeDimAlgebra R d) (x : Fin d → R) :
    m.mul x (one R d) = x := sorry

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
    mulOfStructureConst a (Pi.single i 1) (Pi.single j 1) k = a i j k := sorry

/-- The arrows between distinguished algebra structures in their bundled groupoid. -/
abbrev Hom (m m' : FreeDimAlgebra R d) := m ⟶ m'

namespace Hom

/-- The invertible linear map underlying an algebra arrow. -/
def equiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    LinearMap.GeneralLinearGroup R (Fin d → R) := f.automorphism

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
theorem id_equiv (m : FreeDimAlgebra R d) : (id m).equiv = 1 := sorry

/-- Composition of algebra arrows, with underlying automorphism `f.equiv * g.equiv`. -/
def comp {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    Hom m₁ m₃ := arrowComp f g

/-- The underlying linear automorphism of a composite is the product of the automorphisms. -/
theorem comp_equiv {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    (comp f g).equiv = f.equiv * g.equiv := sorry

/-- The inverse algebra arrow, given by the inverse linear automorphism. -/
def inv {m m' : FreeDimAlgebra R d} (f : Hom m m') : Hom m' m := arrowInv f

/-- The underlying linear automorphism of an inverse arrow is the inverse automorphism. -/
theorem inv_equiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (inv f).equiv = f.equiv⁻¹ := sorry

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
      ∀ x y, m.mul (f.equiv.val x) (f.equiv.val y) = f.equiv.val (m'.mul x y) := sorry

end Hom

private theorem baseChange_laws {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) :
    let b := mulOfStructureConst (fun i j k ↦ f (structureConst m i j k))
    (∀ x y z, b (b x y) z = b x (b y z)) ∧
    (∀ x y, b x y = b y x) ∧ (∀ x, b (one S d) x = x) := sorry

/-- Base change applies a ring homomorphism to the structure constants of multiplication. -/
def baseChange {S : Type u} [CommRing S] (f : R →+* S) (m : FreeDimAlgebra R d) :
    FreeDimAlgebra S d :=
  ofMul (mulOfStructureConst (fun i j k ↦ f (structureConst m i j k)))
    (baseChange_laws f m).1 (baseChange_laws f m).2.1 (baseChange_laws f m).2.2

/-- The structure constants after base change are the images of the original constants. -/
theorem baseChange_structureConst {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) (i j k : Fin d) :
    structureConst (baseChange f m) i j k = f (structureConst m i j k) := sorry

namespace Hom

private theorem baseChange_laws {S : Type u} [CommRing S] (f : R →+* S)
    {m m' : FreeDimAlgebra R d} (φ : Hom m m') :
    let e := Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm φ.equiv))
    e.val (one S d) = one S d ∧
    (∀ x y, (FreeDimAlgebra.baseChange f m).mul (e.val x) (e.val y) =
      e.val ((FreeDimAlgebra.baseChange f m').mul x y)) := sorry

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
      Hom.baseChange f (φ ≫ ψ) = Hom.baseChange f φ ≫ Hom.baseChange f ψ) := sorry

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
    (baseChangeFunctor f).obj m = baseChange f m := sorry

end FreeDimAlgebra
end AlgebraicGeometry
