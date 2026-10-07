module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Defs.Basic

/-!
# Algebras topologically of finite type

An algebra `A` over `R` is topologically of finite type when some `R`-algebra
map from a finite-variable polynomial ring has dense image. This is the density
analogue of `Algebra.FiniteType` and `Algebra.FinitePresentation`, and is
distinct from the `I`-adic `Algebra.TopologicallyFiniteType` of tag 0AL4.
-/

@[expose] public section

universe u v w

variable (R : Type u) (A : Type v)

/-- An algebra is topologically of finite type if some polynomial algebra map
from finitely many variables has dense image. -/
class Algebra.TopologicallyOfFiniteType [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] : Prop where
  /-- There exists an `R`-algebra map from a finite-variable polynomial ring
  with dense image. -/
  out : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f

namespace Algebra
namespace TopologicallyOfFiniteType

variable {R A}
variable [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A]

/-- Algebraically finite-type algebras are topologically of finite type. -/
instance (priority := 100) ofFiniteType [Algebra.FiniteType R A] :
    TopologicallyOfFiniteType R A := sorry

/-- A dense polynomial algebra map witnesses that the target is topologically of
finite type. -/
theorem of_denseRange {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : DenseRange f) :
    TopologicallyOfFiniteType R A := sorry

/-- A topologically finite-type algebra admits a dense polynomial algebra map. -/
theorem exists_denseRange_mvPolynomial [TopologicallyOfFiniteType R A] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f := sorry

/-- Topological finite type is equivalent to the existence of a dense polynomial
algebra map. -/
theorem iff :
    TopologicallyOfFiniteType R A ↔
      ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f := sorry

/-- Topological finite type is equivalent to the existence of a finitely generated
dense subalgebra. -/
theorem iff_dense_adjoin :
    TopologicallyOfFiniteType R A ↔
      ∃ s : Finset A, Dense (Algebra.adjoin R (s : Set A) : Set A) := sorry

end TopologicallyOfFiniteType
end Algebra

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- A ring homomorphism is topologically of finite type if the target is
topologically of finite type over the source. -/
def TopologicallyOfFiniteType (f : A →+* B) : Prop :=
  @Algebra.TopologicallyOfFiniteType A B _ _ f.toAlgebra _

/-- The algebra map is topologically of finite type iff the algebra is. -/
theorem topologicallyOfFiniteType_algebraMap [Algebra A B] :
    (algebraMap A B).TopologicallyOfFiniteType ↔ Algebra.TopologicallyOfFiniteType A B :=
  sorry

end RingHom

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [TopologicalSpace B]

/-- An algebra homomorphism is topologically of finite type if the underlying
ring homomorphism is. -/
def TopologicallyOfFiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.TopologicallyOfFiniteType

/-- An algebra homomorphism is topologically of finite type iff the induced
algebra structure on the target is. -/
theorem topologicallyOfFiniteType_iff (f : A →ₐ[R] B) :
    f.TopologicallyOfFiniteType ↔
      @Algebra.TopologicallyOfFiniteType A B _ _ f.toRingHom.toAlgebra _ := sorry

end AlgHom
