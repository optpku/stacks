module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Free d-dimensional algebras

A free `d`-dimensional algebra over a commutative ring `R` is a commutative unital
`R`-algebra structure on the standard module `Fin d → R` whose unit is the first
basis vector `Pi.single 0 1`. Isomorphisms are invertible `R`-linear maps fixing that
unit and intertwining the multiplications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A commutative unital algebra structure on `Fin d → R` with unit `Pi.single 0 1`. -/
structure FreeDimAlgebra (R : Type u) [CommRing R] (d : ℕ) [NeZero d] where
  /-- The `R`-bilinear multiplication map. -/
  mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R)
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y, mul x y = mul y x
  /-- The vector `Pi.single 0 1` is a left unit for multiplication. -/
  one_mul : ∀ x, mul (Pi.single 0 1) x = x

namespace FreeDimAlgebra

/-- The unit vector `e₁ = (1, 0, …, 0)` of `Fin d → R`. -/
def one (R : Type u) [CommRing R] (d : ℕ) [NeZero d] : Fin d → R :=
  Pi.single 0 1

/-- The unit vector is the first standard basis vector. -/
theorem one_eq (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    one R d = Pi.single 0 1 := sorry

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

/-- Assemble a free `d`-dimensional algebra from a bilinear multiplication and its laws. -/
def ofMul (mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (mul_comm : ∀ x y, mul x y = mul y x)
    (one_mul : ∀ x, mul (one R d) x = x) : FreeDimAlgebra R d where
  mul := mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul

/-- The multiplication of `ofMul mul …` is the supplied bilinear map. -/
theorem ofMul_mul (mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R))
    (mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (mul_comm : ∀ x y, mul x y = mul y x)
    (one_mul : ∀ x, mul (one R d) x = x) :
    (ofMul mul mul_assoc mul_comm one_mul).mul = mul := sorry

/-- A free `d`-dimensional algebra is unital, commutative, and associative. -/
theorem spec (m : FreeDimAlgebra R d) :
    (∀ x, m.mul (one R d) x = x) ∧
      (∀ x y, m.mul x y = m.mul y x) ∧
        (∀ x y z, m.mul (m.mul x y) z = m.mul x (m.mul y z)) := sorry

/-- The unit vector is also a right unit, by commutativity. -/
theorem mul_one (m : FreeDimAlgebra R d) (x : Fin d → R) :
    m.mul x (one R d) = x := sorry

/-- Structure constants `a i j k` of `m`, so that
`m.mul (Pi.single i 1) (Pi.single j 1) k = structureConst m i j k`. -/
def structureConst (m : FreeDimAlgebra R d) (i j k : Fin d) : R :=
  m.mul (Pi.single i 1) (Pi.single j 1) k

/-- Reconstruct bilinear multiplication from structure constants via the standard basis. -/
def mulOfStructureConst (a : Fin d → Fin d → Fin d → R) :
    (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R) :=
  let b := Pi.basisFun R (Fin d)
  b.constr R fun i ↦ b.constr R fun j ↦ fun k ↦ a i j k

/-- Evaluating `mulOfStructureConst a` on a pair of standard basis vectors recovers `a`. -/
theorem mulOfStructureConst_structureConst (a : Fin d → Fin d → Fin d → R)
    (i j k : Fin d) :
    mulOfStructureConst a (Pi.single i 1) (Pi.single j 1) k = a i j k := sorry

/-- An isomorphism of free `d`-dimensional algebras is an invertible linear map
fixing `one R d` and intertwining multiplications by
`m.mul (φ x) (φ y) = φ (m'.mul x y)`. -/
structure Hom (m m' : FreeDimAlgebra R d) where
  /-- The underlying invertible `R`-linear map. -/
  equiv : LinearMap.GeneralLinearGroup R (Fin d → R)
  /-- The linear map fixes the unit vector `one R d`. -/
  map_one : equiv.val (one R d) = one R d
  /-- The source intertwiner `m ∘ (φ ⊗ φ) = φ ∘ m'`. -/
  map_mul : ∀ x y, m.mul (equiv.val x) (equiv.val y) = equiv.val (m'.mul x y)

namespace Hom

/-- Assemble an isomorphism from an invertible linear map and the unit/multiplication laws. -/
def of {m m' : FreeDimAlgebra R d} (e : LinearMap.GeneralLinearGroup R (Fin d → R))
    (map_one : e.val (one R d) = one R d)
    (map_mul : ∀ x y, m.mul (e.val x) (e.val y) = e.val (m'.mul x y)) : Hom m m' where
  equiv := e
  map_one := map_one
  map_mul := map_mul

/-- The identity isomorphism of a free `d`-dimensional algebra. -/
def id (m : FreeDimAlgebra R d) : Hom m m where
  equiv := 1
  map_one := sorry
  map_mul := sorry

/-- The underlying linear automorphism of `id` is the identity. -/
theorem id_equiv (m : FreeDimAlgebra R d) : (id m).equiv = 1 := sorry

/-- Composition of isomorphisms of free `d`-dimensional algebras. -/
def comp {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    Hom m₁ m₃ where
  equiv := f.equiv * g.equiv
  map_one := sorry
  map_mul := sorry

/-- The underlying linear automorphism of a composite is the composite of the automorphisms. -/
theorem comp_equiv {m₁ m₂ m₃ : FreeDimAlgebra R d} (f : Hom m₁ m₂) (g : Hom m₂ m₃) :
    (comp f g).equiv = f.equiv * g.equiv := sorry

/-- The inverse isomorphism, given by the inverse linear automorphism. -/
def inv {m m' : FreeDimAlgebra R d} (f : Hom m m') : Hom m' m where
  equiv := f.equiv⁻¹
  map_one := sorry
  map_mul := sorry

/-- The underlying linear automorphism of `inv f` is the inverse automorphism. -/
theorem inv_equiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (inv f).equiv = f.equiv⁻¹ := sorry

/-- The underlying linear equivalence of an isomorphism of free `d`-dimensional algebras. -/
def toLinearEquiv {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    (Fin d → R) ≃ₗ[R] (Fin d → R) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv f.equiv

/-- The matrix in `GL_d(R)` associated to an isomorphism of free `d`-dimensional algebras. -/
def toGL {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    Matrix.GeneralLinearGroup (Fin d) R :=
  Matrix.GeneralLinearGroup.toLin.symm f.equiv

/-- An isomorphism fixes the unit and intertwines multiplications. -/
theorem spec {m m' : FreeDimAlgebra R d} (f : Hom m m') :
    f.equiv.val (one R d) = one R d ∧
      ∀ x y, m.mul (f.equiv.val x) (f.equiv.val y) = f.equiv.val (m'.mul x y) := sorry

end Hom

/-- Base change of a free `d`-dimensional algebra along a ring homomorphism, by applying
the homomorphism to structure constants. -/
def baseChange {S : Type u} [CommRing S] (f : R →+* S) (m : FreeDimAlgebra R d) :
    FreeDimAlgebra S d where
  mul := mulOfStructureConst (fun i j k ↦ f (structureConst m i j k))
  mul_assoc := sorry
  mul_comm := sorry
  one_mul := sorry

/-- Base change applies the ring homomorphism to structure constants. -/
theorem baseChange_structureConst {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) (i j k : Fin d) :
    structureConst (baseChange f m) i j k = f (structureConst m i j k) := sorry

namespace Hom

/-- Base change of an isomorphism, by applying the ring homomorphism to matrix entries. -/
def baseChange {S : Type u} [CommRing S] (f : R →+* S) {m m' : FreeDimAlgebra R d}
    (φ : Hom m m') : Hom (FreeDimAlgebra.baseChange f m) (FreeDimAlgebra.baseChange f m') where
  equiv :=
    Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.toLin.symm φ.equiv))
  map_one := sorry
  map_mul := sorry

end Hom

/-- The fibre of `FA d` over a ring is a groupoid of free `d`-dimensional algebras. -/
instance groupoid (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    Groupoid (FreeDimAlgebra R d) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := Hom.inv
  inv_comp := sorry
  comp_inv := sorry

/-- The functorial action of a ring homomorphism on free `d`-dimensional algebras. -/
def baseChangeFunctor {S : Type u} [CommRing S] (f : R →+* S) :
    FreeDimAlgebra R d ⥤ FreeDimAlgebra S d where
  obj := baseChange f
  map φ := Hom.baseChange f φ
  map_id := sorry
  map_comp := sorry

/-- On objects, `baseChangeFunctor f` is `baseChange f`. -/
theorem baseChangeFunctor_obj {S : Type u} [CommRing S] (f : R →+* S)
    (m : FreeDimAlgebra R d) :
    (baseChangeFunctor f).obj m = baseChange f m := sorry

end FreeDimAlgebra
end AlgebraicGeometry
