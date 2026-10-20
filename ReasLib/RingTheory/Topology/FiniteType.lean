/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

universe u v w

variable (R : Type u) (A : Type v)

/-- An algebra is topologically of finite type when a finite-variable polynomial
algebra maps densely into it. -/
class Algebra.TopologicallyOfFiniteType [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] : Prop where
  /-- A finite-variable polynomial algebra map with dense range exists. -/
  out : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f

namespace Algebra
namespace TopologicallyOfFiniteType

variable {R A}
variable [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A]

/-- An algebraically finite-type algebra is topologically of finite type. -/
instance (priority := 100) ofFiniteType [Algebra.FiniteType R A] :
    TopologicallyOfFiniteType R A := sorry

/-- A dense finite-variable polynomial algebra map supplies topological finite type. -/
theorem of_denseRange {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : DenseRange f) :
    TopologicallyOfFiniteType R A := sorry

/-- A topologically finite-type algebra has a dense finite-variable polynomial map. -/
theorem exists_denseRange_mvPolynomial [TopologicallyOfFiniteType R A] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f := sorry

/-- Topological finite type is equivalent to admitting a dense finite-variable polynomial map. -/
theorem iff :
    TopologicallyOfFiniteType R A ↔
      ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f := sorry

/-- Topological finite type is equivalent to having a finitely generated dense subalgebra. -/
theorem iff_dense_adjoin :
    TopologicallyOfFiniteType R A ↔
      ∃ s : Finset A, Dense (Algebra.adjoin R (s : Set A) : Set A) := sorry

end TopologicallyOfFiniteType
end Algebra

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- A ring homomorphism is topologically of finite type when its target is so over its source. -/
def TopologicallyOfFiniteType (f : A →+* B) : Prop :=
  @Algebra.TopologicallyOfFiniteType A B _ _ f.toAlgebra _

/-- The algebra-map and ring-homomorphism formulations of topological finite type agree. -/
theorem topologicallyOfFiniteType_algebraMap [Algebra A B] :
    (algebraMap A B).TopologicallyOfFiniteType ↔ Algebra.TopologicallyOfFiniteType A B :=
  sorry

/-- For a continuous map of topological rings, topological finite type is the
dense-range condition for a finite-variable polynomial ring homomorphism. -/
theorem topologicallyOfFiniteType_iff_denseRange
    [TopologicalSpace A] [IsTopologicalRing A] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    φ.TopologicallyOfFiniteType ↔
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) A →+* B),
        g.comp (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) = φ ∧ DenseRange g := sorry

end RingHom

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [TopologicalSpace B]

/-- An algebra homomorphism is topologically of finite type when its underlying ring map is. -/
def TopologicallyOfFiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.TopologicallyOfFiniteType

/-- The algebra-homomorphism predicate agrees with the induced ring-homomorphism algebra. -/
theorem topologicallyOfFiniteType_iff (f : A →ₐ[R] B) :
    f.TopologicallyOfFiniteType ↔
      @Algebra.TopologicallyOfFiniteType A B _ _ f.toRingHom.toAlgebra _ := sorry

end AlgHom
