/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product

/-!
# Exterior products over locally Dedekind schemes

This file constructs the pointwise, cycle-level, degreewise Chow, and total exterior
products over a locally Dedekind base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CycleGroup.Dedekind.ExteriorProduct

/-- The ideal cutting out the product of the reduced closures of two points over a
locally Dedekind base. -/
noncomputable def pointProductIdeal
    {S : Scheme.{u}} (X Y : Over S) (x : X.left) (y : Y.left) :
    (X ⨯ Y).left.IdealSheafData :=
  ((Scheme.PointClosure.reducedStructure x).ideal.comap
      ((Limits.prod.fst : X ⨯ Y ⟶ X)).left) ⊔
    ((Scheme.PointClosure.reducedStructure y).ideal.comap
      ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left)

/-- The product-point ideal is the sum of the pullbacks of the two reduced
point-closure ideals. -/
theorem pointProductIdeal_def
    {S : Scheme.{u}} (X Y : Over S) (x : X.left) (y : Y.left) :
    pointProductIdeal X Y x y =
      ((Scheme.PointClosure.reducedStructure x).ideal.comap
          ((Limits.prod.fst : X ⨯ Y ⟶ X)).left) ⊔
        ((Scheme.PointClosure.reducedStructure y).ideal.comap
          ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left) := rfl

/-- The point contribution in degree `n + m - 1` is the fundamental cycle of the
scheme-theoretic product unless both points lie over closed points of the base. -/
noncomputable def pointProduct
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) :=
  @ite _ (IsClosed ({X.hom.base x} : Set S) ∧ IsClosed ({Y.hom.base y} : Set S))
    (Classical.propDecidable _) 0
    (@Scheme.IdealSheafData.associatedCycle (X ⨯ Y).left
      (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      (pointProductIdeal X Y x y) ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1))

/-- If at least one point lies over a nonclosed base point, its product is the
associated cycle of the product of the two reduced point closures. -/
theorem pointProduct_of_dominates
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m)
    (hdominates : ¬ IsClosed ({X.hom.base x} : Set S) ∨
      ¬ IsClosed ({Y.hom.base y} : Set S)) :
    pointProduct δ h_delta X Y n m x y hx hy =
      @Scheme.IdealSheafData.associatedCycle (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        (pointProductIdeal X Y x y) ((X ⨯ Y).hom.relativeDimensionFunction δ)
        (n + m - 1) := by
  rcases hdominates with hx' | hy'
  · simp [pointProduct, hx']
  · simp [pointProduct, hy']

/-- If both points lie over closed base points, their point-product contribution is zero. -/
theorem pointProduct_of_not_dominates
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m)
    (hx_closed : IsClosed ({X.hom.base x} : Set S))
    (hy_closed : IsClosed ({Y.hom.base y} : Set S)) :
    pointProduct δ h_delta X Y n m x y hx hy = 0 := by
  simp [pointProduct, hx_closed, hy_closed]

/-- The contribution of a pair of points to the exterior product of two cycles. -/
noncomputable def cycleTerm
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m)
    (x : X.left) (y : Y.left) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) :=
  if hx : X.hom.relativeDimensionFunction δ x = n then
    if hy : Y.hom.relativeDimensionFunction δ y = m then
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n alpha x *
          toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) m beta y) •
        pointProduct δ h_delta X Y n m x y hx hy
    else 0
  else 0

/-- At points of the prescribed dimensions, the cycle term is the product of the
two coefficients times the point product. -/
theorem cycleTerm_of_dimensions
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m)
    (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m) :
    cycleTerm δ h_delta X Y n m alpha beta x y =
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n alpha x *
          toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) m beta y) •
        pointProduct δ h_delta X Y n m x y hx hy := by
  simp [cycleTerm, hx, hy]

private theorem associatedCycle_support_subset {T : Scheme.{u}} [IsLocallyNoetherian T]
    (I : T.IdealSheafData) (d : T → ℤ) (k : ℤ) :
    (toAlgebraicCycle d k (I.associatedCycle d k)).support ⊆ I.support := by
  classical
  intro z hz
  by_contra hzI
  apply hz
  change (∑ᶠ ξ : genericPoints I.subscheme,
    @ite ℤ (d (I.subschemeι ξ.1) = k) (Classical.propDecidable _)
      (I.componentCycle ξ z) 0) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro ξ
  have hne : z ≠ I.subschemeι ξ.1 := by
    intro heq
    apply hzI
    rw [heq, ← I.range_subschemeι]
    exact ⟨ξ.1, rfl⟩
  simp [Scheme.IdealSheafData.componentCycle, hne]

/-- The point-pair terms of the cycle exterior product have locally finite support. -/
theorem cycleTermsLocallyFinite
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    LocallyFinite fun p : X.left × Y.left ↦
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
        (cycleTerm δ h_delta X Y n m alpha beta p.1 p.2)).support := by
  classical
  letI : IsLocallyNoetherian (X ⨯ Y).left :=
    LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom
  let f := ((Limits.prod.fst : X ⨯ Y ⟶ X)).left
  let g := ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left
  intro z
  obtain ⟨U, hU, hfinU⟩ :=
    (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n alpha).locallyFiniteSupport (f z)
  obtain ⟨V, hV, hfinV⟩ :=
    (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) m beta).locallyFiniteSupport (g z)
  obtain ⟨U', hU'U, hU', hzU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨V', hV'V, hV', hzV'⟩ := mem_nhds_iff.mp hV
  refine ⟨f ⁻¹' U' ∩ g ⁻¹' V',
    ((hU'.preimage f.continuous).inter (hV'.preimage g.continuous)).mem_nhds
      ⟨hzU', hzV'⟩, (hfinU.prod hfinV).subset ?_⟩
  rintro ⟨x, y⟩ ⟨w, hw, hwU, hwV⟩
  have hx : X.hom.relativeDimensionFunction δ x = n := by
    by_contra h
    simpa [cycleTerm, h] using hw
  have hy : Y.hom.relativeDimensionFunction δ y = m := by
    by_contra h
    simpa [cycleTerm, hx, h] using hw
  have ha : toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n alpha x ≠ 0 := by
    intro h
    simpa [cycleTerm, hx, hy, h] using hw
  have hb : toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) m beta y ≠ 0 := by
    intro h
    simpa [cycleTerm, hx, hy, h] using hw
  have hp : w ∈ (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
      (pointProduct δ h_delta X Y n m x y hx hy)).support := by
    intro hzero
    apply hw
    simp [cycleTerm, hx, hy, map_zsmul, Function.locallyFinsuppWithin.coe_zsmul, hzero]
  have hI : w ∈ (pointProductIdeal X Y x y).support := by
    by_cases hclosed : IsClosed ({X.hom.base x} : Set S) ∧
        IsClosed ({Y.hom.base y} : Set S)
    · simpa [pointProduct, hclosed] using hp
    · apply associatedCycle_support_subset
        (pointProductIdeal X Y x y) ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
      simpa [pointProduct, hclosed] using hp
  have hleft : w ∈ ((Scheme.PointClosure.reducedStructure x).ideal.comap f).support :=
    Scheme.IdealSheafData.support_antitone le_sup_left hI
  have hright : w ∈ ((Scheme.PointClosure.reducedStructure y).ideal.comap g).support :=
    Scheme.IdealSheafData.support_antitone le_sup_right hI
  rw [Scheme.IdealSheafData.support_comap,
    (Scheme.PointClosure.reducedStructure x).support_eq] at hleft
  rw [Scheme.IdealSheafData.support_comap,
    (Scheme.PointClosure.reducedStructure y).support_eq] at hright
  change f w ∈ closure ({x} : Set X.left) at hleft
  change g w ∈ closure ({y} : Set Y.left) at hright
  obtain ⟨a, haU, hax⟩ := mem_closure_iff.mp hleft U' hU' hwU
  obtain ⟨b, hbV, hby⟩ := mem_closure_iff.mp hright V' hV' hwV
  exact ⟨⟨hU'U (by simpa only [Set.mem_singleton_iff.mp hax] using haU), ha⟩,
    ⟨hV'V (by simpa only [Set.mem_singleton_iff.mp hby] using hbV), hb⟩⟩

/-- The cycle exterior product is the locally finite sum of its point-pair terms. -/
noncomputable def cycleValue
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) :=
  locallyFiniteSum ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
    (fun p : X.left × Y.left ↦ cycleTerm δ h_delta X Y n m alpha beta p.1 p.2)
    (cycleTermsLocallyFinite δ h_delta X Y n m alpha beta)

/-- Evaluation of the cycle exterior product is the pointwise locally finite sum of
the point-pair terms. -/
theorem cycleValue_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m)
    (z : (X ⨯ Y).left) :
    toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
        (cycleValue δ h_delta X Y n m alpha beta) z =
      ∑ᶠ p : X.left × Y.left,
        toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
          (cycleTerm δ h_delta X Y n m alpha beta p.1 p.2) z := by
  rfl

/-- The cycle exterior product vanishes when its right input is zero. -/
theorem cycleValue_zero_right
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    cycleValue δ h_delta X Y n m alpha 0 = 0 := by
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
    (cycleValue δ h_delta X Y n m alpha 0) z = 0
  rw [cycleValue_apply]
  simp [cycleTerm]

/-- The cycle exterior product is additive in its right input. -/
theorem cycleValue_add_right
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta gamma : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    cycleValue δ h_delta X Y n m alpha (beta + gamma) =
      cycleValue δ h_delta X Y n m alpha beta +
        cycleValue δ h_delta X Y n m alpha gamma := by
  let c (γ : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m)
      (p : X.left × Y.left) :=
    cycleTerm δ h_delta X Y n m alpha γ p.1 p.2
  have hc (γ : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
      LocallyFinite fun p : X.left × Y.left ↦
        (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
          (c γ p)).support := by
    simpa [c] using cycleTermsLocallyFinite δ h_delta X Y n m alpha γ
  have hadd (p : X.left × Y.left) : c (beta + gamma) p = c beta p + c gamma p := by
    by_cases hx : X.hom.relativeDimensionFunction δ p.1 = n
    · by_cases hy : Y.hom.relativeDimensionFunction δ p.2 = m
      · simp [c, cycleTerm, hx, hy, mul_add, add_smul]
      · simp [c, cycleTerm, hx, hy]
    · simp [c, cycleTerm, hx]
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change (∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c (beta + gamma) p) z) =
    (∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c beta p) z) +
    ∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c gamma p) z
  simp_rw [hadd, map_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  exact finsum_add_distrib ((hc beta).point_finite z) ((hc gamma).point_finite z)

/-- Exterior product by a fixed left cycle, as an additive homomorphism in the right cycle. -/
noncomputable def cycleRight
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m →+
      CycleGroup (X ⨯ Y).left
        ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) where
  toFun := cycleValue δ h_delta X Y n m alpha
  map_zero' := cycleValue_zero_right δ h_delta X Y n m alpha
  map_add' := cycleValue_add_right δ h_delta X Y n m alpha

/-- The right-variable exterior-product homomorphism vanishes at a zero left cycle. -/
theorem cycleRight_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    cycleRight δ h_delta X Y n m 0 = 0 := by
  apply AddMonoidHom.ext
  intro beta
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
      (cycleValue δ h_delta X Y n m 0 beta) z = 0
  rw [cycleValue_apply]
  simp [cycleTerm]

/-- The right-variable exterior-product homomorphism is additive in its left cycle. -/
theorem cycleRight_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha beta : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    cycleRight δ h_delta X Y n m (alpha + beta) =
      cycleRight δ h_delta X Y n m alpha + cycleRight δ h_delta X Y n m beta := by
  apply AddMonoidHom.ext
  intro gamma
  let c (a : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
      (p : X.left × Y.left) :=
    cycleTerm δ h_delta X Y n m a gamma p.1 p.2
  have hc (a : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
      LocallyFinite fun p : X.left × Y.left ↦
        (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
          (c a p)).support := by
    simpa [c] using cycleTermsLocallyFinite δ h_delta X Y n m a gamma
  have hadd (p : X.left × Y.left) : c (alpha + beta) p = c alpha p + c beta p := by
    by_cases hx : X.hom.relativeDimensionFunction δ p.1 = n
    · by_cases hy : Y.hom.relativeDimensionFunction δ p.2 = m
      · simp [c, cycleTerm, hx, hy, add_mul, add_smul]
      · simp [c, cycleTerm, hx, hy]
    · simp [c, cycleTerm, hx]
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change (∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c (alpha + beta) p) z) =
    (∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c alpha p) z) +
    ∑ᶠ p, toAlgebraicCycle
      ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) (c beta p) z
  simp_rw [hadd, map_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  exact finsum_add_distrib ((hc alpha).point_finite z) ((hc beta).point_finite z)

/-- The cycle-level exterior product over a locally Dedekind base as a biadditive pairing. -/
noncomputable def cyclePairing
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n →+
      CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m →+
        CycleGroup (X ⨯ Y).left
          ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1) where
  toFun := cycleRight δ h_delta X Y n m
  map_zero' := cycleRight_zero δ h_delta X Y n m
  map_add' := cycleRight_add δ h_delta X Y n m

/-- The cycle pairing sends point generators to their point product. -/
theorem cyclePairing_point
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m) :
    cyclePairing δ h_delta X Y n m
        (CycleGroup.point (X.hom.relativeDimensionFunction δ) n x hx)
        (CycleGroup.point (Y.hom.relativeDimensionFunction δ) m y hy) =
      pointProduct δ h_delta X Y n m x y hx hy := by
  classical
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
    (cycleValue δ h_delta X Y n m
      (CycleGroup.point (X.hom.relativeDimensionFunction δ) n x hx)
      (CycleGroup.point (Y.hom.relativeDimensionFunction δ) m y hy)) z = _
  rw [cycleValue_apply, finsum_eq_single _ (x, y)]
  · simp [cycleTerm, hx, hy, toAlgebraicCycle, CycleGroup.point]
  · intro p hp
    by_cases hpx : p.1 = x
    · have hpy : p.2 ≠ y := by
        intro h
        exact hp (Prod.ext hpx h)
      simp [cycleTerm, toAlgebraicCycle, CycleGroup.point, hpy]
    · simp [cycleTerm, toAlgebraicCycle, CycleGroup.point, hpx]

end CycleGroup.Dedekind.ExteriorProduct

namespace ChowGroup.Dedekind.ExteriorProduct

/-- For a fixed cycle on `X`, take the Chow class of its cycle exterior product. -/
noncomputable def classRight
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m →+
      @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1) :=
  (@chowClass (X ⨯ Y).left
      (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1)).comp
    (CycleGroup.Dedekind.ExteriorProduct.cyclePairing δ h_delta X Y n m alpha)

/-- For a fixed left cycle, the cycle exterior product kills rational boundaries in
the right variable after passage to Chow classes. -/
theorem boundaries_le_ker_classRight
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    @RationalEquivalence.boundaries Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance m ≤
      (classRight δ h_delta X Y n m alpha).ker := sorry

/-- Exterior product by a fixed left cycle, descended through rational equivalence in
the right variable. -/
noncomputable def right
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance m →+
      @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance m)
    (classRight δ h_delta X Y n m alpha)
    (boundaries_le_ker_classRight δ h_delta X Y n m alpha)

/-- The right-descended exterior product vanishes at a zero left cycle. -/
theorem right_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    right δ h_delta X Y n m 0 = 0 := by
  apply AddMonoidHom.ext
  intro beta
  refine Quotient.inductionOn beta ?_
  intro b
  change classRight δ h_delta X Y n m 0 b = 0
  simp [classRight]

/-- The right-descended exterior product is additive in its left cycle. -/
theorem right_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha beta : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    right δ h_delta X Y n m (alpha + beta) =
      right δ h_delta X Y n m alpha + right δ h_delta X Y n m beta := by
  apply AddMonoidHom.ext
  intro gamma
  refine Quotient.inductionOn gamma ?_
  intro c
  change classRight δ h_delta X Y n m (alpha + beta) c =
    classRight δ h_delta X Y n m alpha c + classRight δ h_delta X Y n m beta c
  simp [classRight]

/-- Exterior product after descent in the right variable, as an additive map of left cycles. -/
noncomputable def fromCycles
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n →+
      @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance m →+
        @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1) where
  toFun := right δ h_delta X Y n m
  map_zero' := right_zero δ h_delta X Y n m
  map_add' := right_add δ h_delta X Y n m

/-- The right-descended product kills rational boundaries in the left variable. -/
theorem boundaries_le_ker_fromCycles
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    @RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance n ≤
      (fromCycles δ h_delta X Y n m).ker := sorry

/-- The degreewise exterior-product pairing on relative Chow groups over a locally
Dedekind base. -/
noncomputable def pairing
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance n →+
      @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance m →+
        @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance n)
    (fromCycles δ h_delta X Y n m)
    (boundaries_le_ker_fromCycles δ h_delta X Y n m)

/-- On represented Chow classes, the descended pairing is represented by the concrete
cycle exterior product. -/
theorem pairing_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    pairing δ h_delta X Y n m
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance n alpha)
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance m beta) =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1)
        (CycleGroup.Dedekind.ExteriorProduct.cyclePairing
          δ h_delta X Y n m alpha beta) := rfl

/-- The Dedekind Chow exterior pairing is balanced over `ℤ`. -/
theorem pairing_zsmul
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m r : ℤ) (alpha : RelativeChow δ X n) (beta : RelativeChow δ Y m) :
    pairing δ h_delta X Y n m (r • alpha) beta =
      pairing δ h_delta X Y n m alpha (r • beta) := by
  simp

end ChowGroup.Dedekind.ExteriorProduct

namespace ChowGroup.Dedekind

/-- The canonical degreewise exterior-product map on Chow groups over a locally Dedekind base. -/
noncomputable def exteriorProduct
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    TensorProduct ℤ (RelativeChow δ X n) (RelativeChow δ Y m) →ₗ[ℤ]
      RelativeChow δ (X ⨯ Y) (n + m - 1) :=
  (TensorProduct.liftAddHom
      (ExteriorProduct.pairing δ h_delta X Y n m)
      (ExteriorProduct.pairing_zsmul δ h_delta X Y n m)).toIntLinearMap

/-- The Dedekind Chow exterior product evaluates on a pure tensor by the descended pairing. -/
theorem exteriorProduct_tmul
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : RelativeChow δ X n) (beta : RelativeChow δ Y m) :
    exteriorProduct δ h_delta X Y n m (alpha ⊗ₜ[ℤ] beta) =
      ExteriorProduct.pairing δ h_delta X Y n m alpha beta := rfl

/-- On Chow classes of cycles, the Dedekind exterior product is represented by the
concrete cycle-level product. -/
theorem exteriorProduct_tmul_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    exteriorProduct δ h_delta X Y n m
        ((@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance n alpha) ⊗ₜ[ℤ]
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance m beta)) =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1)
        (CycleGroup.Dedekind.ExteriorProduct.cyclePairing
          δ h_delta X Y n m alpha beta) := by
  rw [exteriorProduct_tmul, ExteriorProduct.pairing_chowClass]

namespace Total

/-- The exterior product on total relative Chow homology, assembled from the
degreewise exterior-product pairings. -/
noncomputable def exteriorProduct
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    ChowGroup.Total δ X →+ ChowGroup.Total δ Y →+ ChowGroup.Total δ (X ⨯ Y) :=
  DirectSum.toAddMonoid fun n ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun m ↦
      AddMonoidHom.flip <|
        (DirectSum.of (fun d : ℤ ↦
            @ChowGroup (X ⨯ Y).left
              (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
              ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance d)
          (n + m - 1)).compHom.comp
            (ExteriorProduct.pairing δ h_delta X Y n m)

/-- The total exterior product of homogeneous classes is the degreewise exterior
product in degree `n + m - 1`. -/
theorem exteriorProduct_of
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance n)
    (beta : @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance m) :
    exteriorProduct δ h_delta X Y
        (DirectSum.of (fun d : ℤ ↦
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance d) n alpha)
        (DirectSum.of (fun d : ℤ ↦
          @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction δ) inferInstance d) m beta) =
      DirectSum.of (fun d : ℤ ↦
        @ChowGroup (X ⨯ Y).left
          (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance d) (n + m - 1)
        (ExteriorProduct.pairing δ h_delta X Y n m alpha beta) := by
  simp [exteriorProduct, DirectSum.toAddMonoid_of]

end Total

/-- The exterior product on total Chow homology over a locally Dedekind base is
associative after pushforward along the canonical product associator. -/
theorem exteriorProduct_assoc
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (alpha : ChowGroup.Total δ X) (beta : ChowGroup.Total δ Y) (gamma : ChowGroup.Total δ Z) :
    ChowGroup.Total.map δ (Limits.prod.associator X Y Z).hom
        (Total.exteriorProduct δ h_delta (X ⨯ Y) Z
          (Total.exteriorProduct δ h_delta X Y alpha beta) gamma) =
      Total.exteriorProduct δ h_delta X (Y ⨯ Z) alpha
        (Total.exteriorProduct δ h_delta Y Z beta gamma) := sorry

end ChowGroup.Dedekind

end AlgebraicGeometry
