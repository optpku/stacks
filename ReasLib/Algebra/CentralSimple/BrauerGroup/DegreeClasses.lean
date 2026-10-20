/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Degree

@[expose] public section

universe u v

namespace CSA

variable {K : Type u} [Field K]

/-- The subtype of finite central simple `K`-algebras having prescribed degree `d`. -/
def DegreeAlgebra (d : ℕ) : Type (max u (v + 1)) :=
  {A : CSA.{u, v} K // A.degree = d}

/-- Two degree-`d` central simple algebras are isomorphic when they are `K`-algebra equivalent. -/
def DegreeAlgebra.Isomorphic {d : ℕ}
    (A B : DegreeAlgebra.{u, v} (K := K) d) : Prop :=
  Nonempty (A.1 ≃ₐ[K] B.1)

/-- Isomorphism of degree-`d` central simple algebras is an equivalence relation. -/
theorem DegreeAlgebra.isomorphic_equivalence (d : ℕ) :
    Equivalence (DegreeAlgebra.Isomorphic.{u, v} (K := K) (d := d)) := sorry

/-- The setoid of degree-`d` central simple algebras modulo `K`-algebra isomorphism. -/
def degreeAlgebraSetoid (d : ℕ) :
    Setoid (DegreeAlgebra.{u, v} (K := K) d) where
  r := DegreeAlgebra.Isomorphic.{u, v} (K := K) (d := d)
  iseqv := DegreeAlgebra.isomorphic_equivalence.{u, v} (K := K) d

/-- The set of isomorphism classes of degree-`d` central simple `K`-algebras. -/
def degreeAlgebraClasses (d : ℕ) : Type (max u (v + 1)) :=
  Quotient (degreeAlgebraSetoid.{u, v} (K := K) d)

/-- Equality of representatives in the degree-`d` central-simple-algebra quotient. -/
theorem degreeAlgebraClasses_mk_eq_mk_iff (d : ℕ)
    (A B : DegreeAlgebra.{u, v} (K := K) d) :
    Quotient.mk (degreeAlgebraSetoid.{u, v} (K := K) d) A =
      Quotient.mk (degreeAlgebraSetoid.{u, v} (K := K) d) B ↔
      DegreeAlgebra.Isomorphic.{u, v} A B := sorry

end CSA

end
