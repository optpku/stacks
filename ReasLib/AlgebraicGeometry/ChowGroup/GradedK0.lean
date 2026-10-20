/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.Scheme.K0.SupportFiltration
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

open Scheme.K0' Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The cycle-level class in `K₀(Coh≤k(X))` attached to a degree-`k` cycle, as the
difference of the explicit positive and negative coproducts. -/
noncomputable def cycleToUpper :
    CycleGroup X (f.relativeDimensionFunction δ) k →+
      AbelianK0 (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) where
  toFun α :=
    AbelianK0.of (GradedK0.positiveObject f δ k α) -
      AbelianK0.of (GradedK0.negativeObject f δ k α)
  map_zero' := sorry
  map_add' := sorry

/-- `cycleToUpper` is the difference of the positive and negative coproduct classes. -/
theorem cycleToUpper_apply
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    cycleToUpper f δ k α =
      AbelianK0.of (GradedK0.positiveObject f δ k α) -
        AbelianK0.of (GradedK0.negativeObject f δ k α) :=
  sorry

/-- The cycle-level class in `F_k K₀'(X)` obtained by restricting the range of `fromUpper`. -/
noncomputable def cycleToFiltration :
    CycleGroup X (f.relativeDimensionFunction δ) k →+
      Scheme.K0'.supportFiltration f δ k :=
  (Scheme.K0'.fromUpper f δ k).rangeRestrict.comp (cycleToUpper f δ k)

/-- `cycleToFiltration` is `fromUpper` range-restricted after the positive/negative
coproduct class. -/
theorem cycleToFiltration_def
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    cycleToFiltration f δ k α =
      (Scheme.K0'.fromUpper f δ k).rangeRestrict (cycleToUpper f δ k α) :=
  sorry

/-- Rational-equivalence boundaries lie in the kernel of the composite to `gr_k K₀'(X)`. -/
theorem rationalBoundaries_le_toGradedK0'_ker :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k ≤
      ((QuotientAddGroup.mk'
            (AddSubgroup.comap (Scheme.K0'.supportFiltration f δ k).subtype
              (Scheme.K0'.supportFiltration f δ (k - 1)))).comp
        (cycleToFiltration f δ k)).ker :=
  sorry

/-- The canonical map `CH_k(X) → gr_k K₀'(X)` sending `[Z]` to the class of `𝒪_Z`. -/
noncomputable def toGradedK0' :
    @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      Scheme.K0'.Graded f δ k :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian f)
      (f.relativeDimensionFunction δ) inferInstance k)
    ((QuotientAddGroup.mk'
        (AddSubgroup.comap (Scheme.K0'.supportFiltration f δ k).subtype
          (Scheme.K0'.supportFiltration f δ (k - 1)))).comp
      (cycleToFiltration f δ k))
    (rationalBoundaries_le_toGradedK0'_ker f δ k)

/-- The canonical map is induced by the cycle-level filtration class. -/
theorem toGradedK0'_comp_chowClass :
    (toGradedK0' f δ k).comp
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k) =
      (QuotientAddGroup.mk'
          (AddSubgroup.comap (Scheme.K0'.supportFiltration f δ k).subtype
            (Scheme.K0'.supportFiltration f δ (k - 1)))).comp
        (cycleToFiltration f δ k) :=
  sorry

/-- On a cycle class, `toGradedK0'` is the associated-graded class of the filtration
image. -/
theorem toGradedK0'_apply
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    toGradedK0' f δ k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k α) =
      Scheme.K0'.Graded.mk f δ k (cycleToFiltration f δ k α) :=
  sorry

/-- The `ℚ`-linear extension `CH_k(X) ⊗ ℚ → gr_k K₀'(X) ⊗ ℚ`. -/
noncomputable def toGradedK0'_tensorQ :
    TensorProduct ℤ
        (@AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
          (f.relativeDimensionFunction δ) inferInstance k) ℚ →+
      TensorProduct ℤ (Scheme.K0'.Graded f δ k) ℚ :=
  (LinearMap.rTensor ℚ (toGradedK0' f δ k).toIntLinearMap).toAddMonoidHom

/-- `toGradedK0'_tensorQ` is the right tensor extension of `toGradedK0'` by `ℚ`. -/
theorem toGradedK0'_tensorQ_def :
    toGradedK0'_tensorQ f δ k =
      (LinearMap.rTensor ℚ (toGradedK0' f δ k).toIntLinearMap).toAddMonoidHom :=
  sorry

/-- For a scheme admitting a closed immersion into a regular quasi-compact ambient
scheme, the rational cycle map to each associated graded coherent K-group is bijective. -/
theorem toGradedK0'_bijective {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
    [CompactSpace Y.left] (k : ℤ) :
    Function.Bijective (toGradedK0'_tensorQ X.hom δ k) :=
  sorry

end AlgebraicGeometry.ChowGroup
