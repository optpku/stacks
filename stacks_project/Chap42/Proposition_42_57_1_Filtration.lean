/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0
public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property

/-!
# Support filtration on coherent `K₀`

This file owns the filtration `F_k K₀'(X) = Im(K₀(Coh≤k(X)) → K₀'(X))` by dimension of
supports, the associated graded pieces `gr_k K₀'(X)`, and the canonical cycle map
`CH_k(X) → gr_k K₀'(X)`.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Short-exact relations in `Coh≤k(X)` vanish in coherent `K₀'(X)`. -/
theorem fromUpper_relations (k : ℤ) :
    AbelianK0.relations
        (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) ≤
      (FreeAbelianGroup.lift fun
          F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj).ker :=
  sorry

/-- The canonical map `K₀(Coh≤k(X)) → K₀'(X)` sending a bounded-support coherent sheaf to
its class in coherent `K₀`. -/
noncomputable def fromUpper (k : ℤ) :
    AbelianK0 (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) →+
      @K0' X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  AbelianK0.lift
    (fun F ↦
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj)
    (fromUpper_relations f δ k)

/-- `fromUpper` sends an object of `Coh≤k(X)` to the coherent Grothendieck class of its
underlying sheaf. -/
theorem fromUpper_of (k : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    fromUpper f δ k (AbelianK0.of F) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F.obj :=
  sorry

/-- The filtration by dimension of supports: `F_k K₀'(X)` is the image of
`K₀(Coh≤k(X)) → K₀'(X)`. -/
noncomputable def supportFiltration (k : ℤ) :
    AddSubgroup (@K0' X (LocallyOfFiniteType.isLocallyNoetherian f)) :=
  (fromUpper f δ k).range

/-- Membership in `F_k K₀'(X)` is being the image of a class from `K₀(Coh≤k(X))`. -/
theorem mem_supportFiltration (k : ℤ)
    (x : @K0' X (LocallyOfFiniteType.isLocallyNoetherian f)) :
    x ∈ supportFiltration f δ k ↔ ∃ y, fromUpper f δ k y = x :=
  sorry

/-- The support filtration is increasing in the dimension bound. -/
theorem supportFiltration_mono {k l : ℤ} (h : k ≤ l) :
    supportFiltration f δ k ≤ supportFiltration f δ l :=
  sorry

/-- The associated graded piece `gr_k K₀'(X) = F_k K₀'(X) / F_{k-1} K₀'(X)`. -/
abbrev Graded (k : ℤ) : Type (u + 1) :=
  supportFiltration f δ k ⧸
    AddSubgroup.comap (supportFiltration f δ k).subtype (supportFiltration f δ (k - 1))

/-- `Graded` is the quotient of `F_k` by the inverse image of `F_{k-1}`. -/
theorem Graded_def (k : ℤ) :
    Graded f δ k =
      (supportFiltration f δ k ⧸
        AddSubgroup.comap (supportFiltration f δ k).subtype
          (supportFiltration f δ (k - 1))) :=
  sorry

/-- The class of an element of `F_k K₀'(X)` in the associated graded piece. -/
noncomputable def Graded.mk (k : ℤ) (x : supportFiltration f δ k) :
    Graded f δ k :=
  QuotientAddGroup.mk' _ x

/-- `Graded.mk` is the canonical quotient class. -/
theorem Graded.mk_def (k : ℤ) (x : supportFiltration f δ k) :
    Graded.mk f δ k x = QuotientAddGroup.mk' _ x :=
  sorry

end AlgebraicGeometry.Scheme.K0'

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

end AlgebraicGeometry.ChowGroup
