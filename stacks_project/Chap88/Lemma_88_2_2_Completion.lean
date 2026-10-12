/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap87.Remark_87_28_2_RestrictedPowerSeries
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Completions of finite type algebras in C'

The `I`-adic completion of a finite type algebra over a Noetherian ring lies
in `C'`, including the polynomial completions `A[x_1, …, x_r]^∧`.
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra.TopologicallyFiniteType

/-- The `I`-adic completion of a finite type `A`-algebra is topologically of
finite type with respect to `I`. -/
instance instOfFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    TopologicallyFiniteType I (AdicCompletion (I.map (algebraMap A C)) C) :=
  sorry

/-- The polynomial completions `A[x_1, …, x_r]^∧` are topologically of finite
type over a Noetherian ring. -/
instance instMvPolynomial {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) : TopologicallyFiniteType I (IAdicRestrictedPowerSeries (Fin r) I) :=
  sorry

end Algebra.TopologicallyFiniteType

namespace CommAlgCat.TopologicallyFiniteType

/-- The `I`-adic completion of a finite type `A`-algebra, as an object of `C'`. -/
def ofFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    TopologicallyFiniteType.{u} A I :=
  of A I (AdicCompletion (I.map (algebraMap A C)) C)

/-- The underlying algebra of `ofFiniteType` is the `I`-adic completion of `C`. -/
theorem ofFiniteType_obj {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    (ofFiniteType I C).obj =
      CommAlgCat.of A (AdicCompletion (I.map (algebraMap A C)) C) :=
  sorry

end CommAlgCat.TopologicallyFiniteType
