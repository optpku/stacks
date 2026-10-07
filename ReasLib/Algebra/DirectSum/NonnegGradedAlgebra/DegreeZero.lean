module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom

/-!
# Degree-zero algebras of nonnegatively graded algebras

The degree-zero piece of a strictly graded-commutative algebra is an ordinary commutative
algebra.  This file packages that canonical structure and the degree-zero algebra homomorphism
induced by every graded homomorphism.
-/

@[expose] public section

noncomputable section

open scoped DirectSum
open CategoryTheory

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)

/-- The ordinary algebra carried by the homogeneous piece of degree zero. -/
@[stacks 09PK "infrastructure: degree-zero algebra of a nonnegative graded algebra"]
abbrev degreeZero : Type v :=
  A.piece 0

/-- Multiplication on the degree-zero piece is commutative. -/
theorem degreeZero_mul_comm (x y : A.degreeZero) : x * y = y * x := sorry

/-- The canonical commutative-semiring structure on the degree-zero piece. -/
noncomputable instance degreeZeroCommSemiring : CommSemiring A.degreeZero where
  mul_comm := A.degreeZero_mul_comm

/-- The graded structural map sends one to the degree-zero unit. -/
theorem degreeZeroAlgebraMap_one :
    DirectSum.GAlgebra.toFun (R := R) (A := A.piece) 1 = (1 : A.degreeZero) := sorry

/-- The graded structural map preserves multiplication in degree zero. -/
theorem degreeZeroAlgebraMap_mul (r s : R) :
    DirectSum.GAlgebra.toFun (R := R) (A := A.piece) (r * s) =
      DirectSum.GAlgebra.toFun (R := R) (A := A.piece) r *
        DirectSum.GAlgebra.toFun (R := R) (A := A.piece) s := sorry

/-- The structural ring homomorphism into the degree-zero piece. -/
def degreeZeroAlgebraMap : R →+* A.degreeZero where
  toFun := DirectSum.GAlgebra.toFun
  map_zero' := map_zero _
  map_one' := A.degreeZeroAlgebraMap_one
  map_add' := map_add _
  map_mul' := A.degreeZeroAlgebraMap_mul

/-- The canonical commutative-ring structure on the degree-zero piece. -/
noncomputable instance degreeZeroCommRing : CommRing A.degreeZero :=
  RingHom.commSemiringToCommRing A.degreeZeroAlgebraMap

/-- The degree-zero structural map has central image. -/
theorem degreeZeroAlgebraMap_commutes (r : R) (x : A.degreeZero) :
    A.degreeZeroAlgebraMap r * x = x * A.degreeZeroAlgebraMap r := sorry

/-- The original graded scalar action agrees with multiplication by the degree-zero structural
map. -/
theorem degreeZeroAlgebraMap_smul (r : R) (x : A.degreeZero) :
    r • x = A.degreeZeroAlgebraMap r * x := sorry

/-- The canonical `R`-algebra structure on the degree-zero piece, retaining the scalar action of
the graded algebra. -/
noncomputable instance degreeZeroAlgebra : Algebra R A.degreeZero where
  algebraMap := A.degreeZeroAlgebraMap
  commutes' := A.degreeZeroAlgebraMap_commutes
  smul_def' := A.degreeZeroAlgebraMap_smul

/-- The algebra map of the degree-zero algebra is the graded structural map. -/
@[simp] theorem algebraMap_degreeZero (r : R) :
    algebraMap R A.degreeZero r =
      DirectSum.GAlgebra.toFun (R := R) (A := A.piece) r := sorry

namespace Hom

variable {A B C : NonnegGradedAlgebra.{u, v} R}

/-- A graded homomorphism preserves the ordinary unit in degree zero. -/
theorem degreeZero_map_one (f : Hom A B) :
    f.map 0 (1 : A.degreeZero) = (1 : B.degreeZero) := sorry

/-- A graded homomorphism preserves ordinary multiplication in degree zero. -/
theorem degreeZero_map_mul (f : Hom A B) (x y : A.degreeZero) :
    f.map 0 (x * y) = f.map 0 x * f.map 0 y := sorry

/-- A graded homomorphism preserves the degree-zero structural algebra map. -/
theorem degreeZero_map_algebraMap (f : Hom A B) (r : R) :
    f.map 0 (algebraMap R A.degreeZero r) = algebraMap R B.degreeZero r := sorry

/-- The algebra homomorphism on degree-zero pieces induced by a graded homomorphism. -/
def degreeZero (f : Hom A B) : A.degreeZero →ₐ[R] B.degreeZero where
  toFun := f.map 0
  map_zero' := map_zero _
  map_one' := f.degreeZero_map_one
  map_add' := map_add _
  map_mul' := f.degreeZero_map_mul
  commutes' := f.degreeZero_map_algebraMap

/-- The induced degree-zero algebra homomorphism is the degree-zero homogeneous map. -/
@[simp] theorem degreeZero_apply (f : Hom A B) (x : A.degreeZero) :
    f.degreeZero x = f.map 0 x := sorry

/-- The identity graded homomorphism induces the identity algebra homomorphism in degree zero. -/
@[simp] theorem degreeZero_id (A : NonnegGradedAlgebra.{u, v} R) :
    (id A).degreeZero = AlgHom.id R A.degreeZero := sorry

/-- Degree-zero algebra homomorphisms preserve composition of graded homomorphisms. -/
@[simp] theorem degreeZero_comp (g : Hom B C) (f : Hom A B) :
    (comp g f).degreeZero = g.degreeZero.comp f.degreeZero := sorry

end Hom

/-- The categorical identity induces the identity morphism on degree-zero algebras. -/
theorem degreeZeroFunctor_map_id (A : NonnegGradedAlgebra.{u, v} R) :
    CommAlgCat.ofHom (Hom.id A).degreeZero =
      𝟙 (CommAlgCat.of R A.degreeZero) := sorry

/-- Categorical composition induces composition on degree-zero algebras. -/
theorem degreeZeroFunctor_map_comp {A B C : NonnegGradedAlgebra.{u, v} R}
    (f : A ⟶ B) (g : B ⟶ C) :
    CommAlgCat.ofHom (Hom.comp g f).degreeZero =
      CommAlgCat.ofHom (f : Hom A B).degreeZero ≫
        CommAlgCat.ofHom (g : Hom B C).degreeZero := sorry

/-- Take the ordinary commutative algebra in degree zero of a nonnegatively graded algebra. -/
@[stacks 09PK "infrastructure: degree-zero functor for nonnegative graded algebras"]
def degreeZeroFunctor (R : Type u) [CommRing R] :
    NonnegGradedAlgebra.{u, v} R ⥤ CommAlgCat.{v} R where
  obj A := CommAlgCat.of R A.degreeZero
  map f := CommAlgCat.ofHom (f : Hom _ _).degreeZero
  map_id A := degreeZeroFunctor_map_id A
  map_comp f g := degreeZeroFunctor_map_comp f g

/-- The degree-zero functor returns the canonical degree-zero algebra. -/
@[simp] theorem degreeZeroFunctor_obj (A : NonnegGradedAlgebra.{u, v} R) :
    (degreeZeroFunctor R).obj A = CommAlgCat.of R A.degreeZero := sorry

/-- The degree-zero functor maps a graded homomorphism by its degree-zero algebra map. -/
@[simp] theorem degreeZeroFunctor_map {A B : NonnegGradedAlgebra.{u, v} R}
    (f : A ⟶ B) :
    (degreeZeroFunctor R).map f =
      CommAlgCat.ofHom (f : Hom A B).degreeZero := sorry

/-- Evaluation of the degree-zero functor is evaluation of the degree-zero homogeneous map. -/
@[simp] theorem degreeZeroFunctor_map_apply
    {A B : NonnegGradedAlgebra.{u, v} R} (f : A ⟶ B) (x : A.degreeZero) :
    (degreeZeroFunctor R).map f x = (f : Hom A B).map 0 x := sorry

end NonnegGradedAlgebra
