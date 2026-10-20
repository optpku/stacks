/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- Evaluate the degree-`n` augmented Newton polynomial in the rank and Chern classes
of a finite locally free module. -/
noncomputable def value {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree] (n : ℕ) :
    ChowCohomology.Nonnegative.degree δ f n :=
  DirectSum.component ℤ ℕ (ChowCohomology.Nonnegative.degree δ f) n
    (ChernPolynomial.eval δ f classes E (augmented n)).1

/-- Embedding the Newton value into total nonnegative Chow cohomology recovers
evaluation of the augmented Newton polynomial. -/
theorem value_spec {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree] (n : ℕ) :
    ChernClass.homogeneous δ f n (value δ f classes E n) =
      (ChernPolynomial.eval δ f classes E (augmented n)).1 := sorry

/-- The degree-zero Newton value is the rank class after embedding into total
nonnegative Chow cohomology. -/
theorem value_zero {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChernClass.homogeneous δ f 0 (value δ f classes E 0) =
      ChernClass.homogeneous δ f 0 (ChernClass.rankClass δ f E) := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
