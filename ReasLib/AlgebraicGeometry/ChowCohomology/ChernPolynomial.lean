module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The homogeneous rank class is central in nonnegative Chow cohomology. -/
theorem rankClass_mem_center (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChernClass.homogeneous δ p 0 (ChernClass.rankClass δ p E) ∈
      Set.center (ChowCohomology.Nonnegative.ring δ p) := sorry

/-- The values of the variables in a universal Chern polynomial: variable zero is
the rank class, while variable `i + 1` is the `(i + 1)`st Chern class. -/
noncomputable def variableValue (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ℕ → Subring.center (ChowCohomology.Nonnegative.ring δ p)
  | 0 =>
      ⟨ChernClass.homogeneous δ p 0 (ChernClass.rankClass δ p E),
        rankClass_mem_center δ p E⟩
  | i + 1 =>
      ⟨ChernClass.homogeneous δ p (i + 1) (classes.component E (i + 1)),
        classes.component_mem_center (Over.mk p) E (i + 1)⟩

/-- Variable zero evaluates to the homogeneous rank class. -/
theorem variableValue_zero (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    (variableValue δ p classes E 0).1 =
      ChernClass.homogeneous δ p 0 (ChernClass.rankClass δ p E) := sorry

/-- A positive-index variable evaluates to the corresponding homogeneous Chern class. -/
theorem variableValue_succ (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    (variableValue δ p classes E (i + 1)).1 =
      ChernClass.homogeneous δ p (i + 1) (classes.component E (i + 1)) := sorry

/-- Evaluate an integer Chern polynomial in the rank and Chern classes of `E`, with
the result retained in the center of nonnegative Chow cohomology. -/
noncomputable def eval (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] (P : MvPolynomial ℕ ℤ) :
    Subring.center (ChowCohomology.Nonnegative.ring δ p) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (variableValue δ p classes E) P

/-- Evaluating variable zero gives the rank-class value. -/
theorem eval_X_zero (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    eval δ p classes E (MvPolynomial.X 0) = variableValue δ p classes E 0 := sorry

/-- Evaluating a positive-index variable gives the corresponding Chern-class value. -/
theorem eval_X_succ (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    eval δ p classes E (MvPolynomial.X (i + 1)) =
      variableValue δ p classes E (i + 1) := sorry

/-- The degree-`n` Chow class obtained by evaluating a weighted-homogeneous Chern
polynomial and projecting to degree `n`. -/
noncomputable def homogeneousValue (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] (P : MvPolynomial ℕ ℤ) (n : ℕ)
    (_ : MvPolynomial.IsWeightedHomogeneous id P n) :
    ChowCohomology.Nonnegative.degree δ p n :=
  DirectSum.component ℤ ℕ (ChowCohomology.Nonnegative.degree δ p) n
    (eval δ p classes E P).1

/-- Embedding `homogeneousValue` in the total ring recovers the full polynomial
evaluation. -/
theorem homogeneousValue_spec (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] (P : MvPolynomial ℕ ℤ) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous id P n) :
    ChernClass.homogeneous δ p n (homogeneousValue δ p classes E P n hP) =
      (eval δ p classes E P).1 := sorry

end AlgebraicGeometry.ChernPolynomial
