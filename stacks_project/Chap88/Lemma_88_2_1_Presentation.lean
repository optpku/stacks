module

public import stacks_project.Chap87.Remark_87_28_2_RestrictedPowerSeries
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Polynomial completions as topologically finite type algebras

The `I`-adic completions `A[x_1, …, x_r]^∧` of finite-variable polynomial
rings, realized as `IAdicRestrictedPowerSeries (Fin r) I`, and the existence
of presentations of objects of `C'` as quotients of such completions.
-/

@[expose] public section

open CommAlgCat.TopologicallyFiniteType

noncomputable section

universe u

namespace Algebra.TopologicallyFiniteType

variable {A : Type u} [CommRing A]

/-- The completions `A[x_1, …, x_r]^∧` are topologically of finite type with
respect to a finitely generated ideal `I`. -/
instance instPolynomialCompletion (I : Ideal A) [hI : Fact I.FG] (r : ℕ) :
    TopologicallyFiniteType I (IAdicRestrictedPowerSeries (Fin r) I) :=
  sorry

/-- An object of `C'` admits a surjective `A`-algebra map from some polynomial
completion `A[x_1, …, x_r]^∧`. -/
theorem exists_surjective_from_polynomialCompletion (I : Ideal A) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    ∃ (r : ℕ) (f : IAdicRestrictedPowerSeries (Fin r) I →ₐ[A] B),
      Function.Surjective f :=
  sorry

/-- An object of `C'` is isomorphic to a quotient of some polynomial
completion `A[x_1, …, x_r]^∧`. -/
theorem exists_isQuotient_polynomialCompletion (I : Ideal A) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    ∃ (r : ℕ) (J : Ideal (IAdicRestrictedPowerSeries (Fin r) I)),
      Nonempty (B ≃ₐ[A] IAdicRestrictedPowerSeries (Fin r) I ⧸ J) :=
  sorry

end Algebra.TopologicallyFiniteType

namespace CommAlgCat.TopologicallyFiniteType

variable {A : Type u} [CommRing A]

/-- The polynomial completion `A[x_1, …, x_r]^∧` as an object of `C'`. -/
def mvPolynomialCompletion (I : Ideal A) (hI : I.FG) (r : ℕ) :
    TopologicallyFiniteType.{u} A I :=
  ⟨CommAlgCat.of A (IAdicRestrictedPowerSeries (Fin r) I),
    Algebra.TopologicallyFiniteType.instPolynomialCompletion (I := I) (hI := ⟨hI⟩) r⟩

/-- The underlying algebra of `mvPolynomialCompletion` is the `I`-adic
restricted power series ring on `r` variables. -/
theorem mvPolynomialCompletion_obj (I : Ideal A) (hI : I.FG) (r : ℕ) :
    (mvPolynomialCompletion I hI r).obj =
      CommAlgCat.of A (IAdicRestrictedPowerSeries (Fin r) I) :=
  sorry

end CommAlgCat.TopologicallyFiniteType
