module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Rational
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- The Newton class `Pᵢ(E)` in the nonnegative Chow-cohomology ring, obtained by
homogeneously embedding the degree-`i` Newton-polynomial value. -/
noncomputable def newtonClass
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    ChowCohomology.Nonnegative.ring δ p :=
  ChernClass.homogeneous δ p i (ChernPolynomial.Newton.value δ p classes E i)

/-- The degree-zero Newton class is the homogeneous rank class. -/
theorem newtonClass_zero
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] :
    newtonClass δ p classes E 0 =
      ChernClass.homogeneous δ p 0 (ChernClass.rankClass δ p E) := sorry

/-- The successor Newton class satisfies the Newton-polynomial recurrence in the
Chern-class components. -/
theorem newtonClass_succ
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (n : ℕ) :
    newtonClass δ p classes E (n + 1) =
      (∑ j ∈ Finset.range n,
        ((-1 : ℤ) ^ j) •
          (ChernClass.homogeneous δ p (j + 1) (classes.component E (j + 1)) *
            newtonClass δ p classes E (n - j))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) •
          ChernClass.homogeneous δ p (n + 1) (classes.component E (n + 1))) := sorry

/-- The degree-`i` Chern-character component `chᵢ(E) = Pᵢ(E) / i!` in
`Aⁱ(X) ⊗[ℤ] ℚ`. -/
noncomputable def characterComponent
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ p i) ℚ :=
  TensorProduct.tmul ℤ (newtonClass δ p classes E i i) ((i.factorial : ℚ)⁻¹)

/-- The Chern-character component is the rationalized degree-`i` Newton class divided
by `i!`. -/
theorem characterComponent_def
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    characterComponent δ p classes E i =
      TensorProduct.tmul ℤ (newtonClass δ p classes E i i) ((i.factorial : ℚ)⁻¹) := sorry

/-- The full Chern character as its family of rational Chow-cohomology components. -/
noncomputable def character
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChowCohomology.Nonnegative.RationalCompletion δ p :=
  fun i ↦ characterComponent δ p classes E i

/-- The degree-`i` value of the full Chern character is its corresponding component. -/
theorem character_apply
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    character δ p classes E i = characterComponent δ p classes E i := sorry

/-- The finite sum of Chern-character components through degree `d`, regarded as a
rationalized total nonnegative Chow-cohomology class. -/
noncomputable def totalCharacter
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (d : ℕ) :
    TensorProduct ℤ (ChowCohomology.Nonnegative.ring δ p) ℚ :=
  ∑ i ∈ Finset.range (d + 1),
    ChowCohomology.Nonnegative.rationalHomogeneous δ p i (character δ p classes E i)

end AlgebraicGeometry.ChernClass.Theory
