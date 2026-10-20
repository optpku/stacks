/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Chow
public import ReasLib.AlgebraicGeometry.ChowGroup.GradedK0
import StacksCheckRecall

/-!
# Proposition 42.57.1

The composition of `ℱ ↦ ℱ[0]`, localized Chern character, and cap against `[Y]`
induces `K₀'(X) ⊗ ℚ ≃ CH_*(X) ⊗ ℚ`, depending on the regular quasi-compact
ambient `Y`. In the same setting, the canonical map `CH_k(X) ⊗ ℚ → gr_k K₀'(X) ⊗ ℚ` is
an isomorphism of `ℚ`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Proposition 42.57.1 (1): The rational coherent-to-Chow comparison for a closed
immersion into a regular quasi-compact ambient scheme is bijective. -/
@[stacks 0FEW] #check (AlgebraicGeometry.Scheme.K0'.toRationalChow_bijective :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
    [CompactSpace Y.left],
    Function.Bijective (AlgebraicGeometry.Scheme.K0'.canonicalToRationalChow_tensorQ δ i))

/- Proposition 42.57.1 (2): In every integer degree, the canonical rational cycle map
to the associated graded coherent K-group is bijective. -/
@[stacks 0FEW] #check (AlgebraicGeometry.ChowGroup.toGradedK0'_bijective :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
    [CompactSpace Y.left] (k : ℤ),
    Function.Bijective (AlgebraicGeometry.ChowGroup.toGradedK0'_tensorQ X.hom δ k))
