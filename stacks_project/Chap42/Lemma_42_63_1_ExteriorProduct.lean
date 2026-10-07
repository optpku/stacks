module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import stacks_project.Chap42.Lemma_42_61_1_ExteriorProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CycleGroup.Dedekind

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
          ((Limits.prod.snd : X ⨯ Y ⟶ Y)).left) := sorry

/-- The degree-`n + m - 1` contribution of two points over a locally Dedekind base.
It is the fundamental cycle of their scheme-theoretic product when at least one point
lies over a nonclosed point of the base, and it is zero otherwise. -/
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

/-- When one point lies over a nonclosed base point, `pointProduct` is the associated
cycle of the scheme-theoretic product of the reduced point closures. -/
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
        (n + m - 1) := sorry

/-- When both points lie over closed base points, their contribution to the Dedekind
exterior product is zero. -/
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
    pointProduct δ h_delta X Y n m x y hx hy = 0 := sorry

/-- The contribution of a pair of points to the Dedekind exterior product of two cycles. -/
noncomputable def exteriorProductTerm
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

/-- For points of the prescribed dimensions, the corresponding exterior-product term
is their coefficient product times `pointProduct`. -/
theorem exteriorProductTerm_of_dimensions
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
    exteriorProductTerm δ h_delta X Y n m alpha beta x y =
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n alpha x *
          toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) m beta y) •
        pointProduct δ h_delta X Y n m x y hx hy := sorry

/-- The point-pair terms in the Dedekind exterior-product formula have locally finite support. -/
theorem exteriorProductTermsLocallyFinite
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
        (exteriorProductTerm δ h_delta X Y n m alpha beta p.1 p.2)).support := sorry

/-- The concrete Dedekind exterior product of two cycles, formed as the locally finite
sum over pairs of points. -/
noncomputable def exteriorProductValue
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
    (fun p : X.left × Y.left ↦
      exteriorProductTerm δ h_delta X Y n m alpha beta p.1 p.2)
    (exteriorProductTermsLocallyFinite δ h_delta X Y n m alpha beta)

/-- The concrete Dedekind exterior product is the locally finite sum of its point-pair
terms. -/
theorem exteriorProductValue_apply
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
        (exteriorProductValue δ h_delta X Y n m alpha beta) z =
      ∑ᶠ p : X.left × Y.left,
        toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction δ) (n + m - 1)
          (exteriorProductTerm δ h_delta X Y n m alpha beta p.1 p.2) z := sorry

/-- The concrete Dedekind exterior product vanishes when its right input is zero. -/
theorem exteriorProductValue_zero_right
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    exteriorProductValue δ h_delta X Y n m alpha 0 = 0 := sorry

/-- The concrete Dedekind exterior product is additive in its right input. -/
theorem exteriorProductValue_add_right
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta gamma : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    exteriorProductValue δ h_delta X Y n m alpha (beta + gamma) =
      exteriorProductValue δ h_delta X Y n m alpha beta +
        exteriorProductValue δ h_delta X Y n m alpha gamma := sorry

/-- Exterior product by a fixed left cycle, as an additive homomorphism in the right cycle. -/
noncomputable def exteriorProductRight
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
  toFun := exteriorProductValue δ h_delta X Y n m alpha
  map_zero' := exteriorProductValue_zero_right δ h_delta X Y n m alpha
  map_add' := exteriorProductValue_add_right δ h_delta X Y n m alpha

/-- The right-variable exterior-product homomorphism vanishes at a zero left cycle. -/
theorem exteriorProductRight_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    exteriorProductRight δ h_delta X Y n m 0 = 0 := sorry

/-- The right-variable exterior-product homomorphism is additive in its left cycle. -/
theorem exteriorProductRight_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha beta : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    exteriorProductRight δ h_delta X Y n m (alpha + beta) =
      exteriorProductRight δ h_delta X Y n m alpha +
        exteriorProductRight δ h_delta X Y n m beta := sorry

/-- The cycle-level exterior product over a locally Dedekind base as a biadditive pairing. -/
noncomputable def exteriorProductPairing
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
  toFun := exteriorProductRight δ h_delta X Y n m
  map_zero' := exteriorProductRight_zero δ h_delta X Y n m
  map_add' := exteriorProductRight_add δ h_delta X Y n m

/-- The cycle pairing sends point generators to their Dedekind point product. -/
theorem exteriorProductPairing_point
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (x : X.left) (y : Y.left)
    (hx : X.hom.relativeDimensionFunction δ x = n)
    (hy : Y.hom.relativeDimensionFunction δ y = m) :
    exteriorProductPairing δ h_delta X Y n m
        (CycleGroup.point (X.hom.relativeDimensionFunction δ) n x hx)
        (CycleGroup.point (Y.hom.relativeDimensionFunction δ) m y hy) =
      pointProduct δ h_delta X Y n m x y hx hy := sorry

end CycleGroup.Dedekind

namespace ChowGroup.Dedekind

/-- For a fixed cycle on `X`, take the Chow class of its Dedekind cycle exterior product. -/
noncomputable def exteriorProductClassRight
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m →+
      RelativeChow δ (X ⨯ Y) (n + m - 1) :=
  (@chowClass (X ⨯ Y).left
      (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1)).comp
    (CycleGroup.Dedekind.exteriorProductPairing δ h_delta X Y n m alpha)

/-- For a fixed left cycle, the Dedekind exterior product kills rational boundaries in
the right variable. -/
theorem boundaries_le_ker_exteriorProductClassRight
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
      (exteriorProductClassRight δ h_delta X Y n m alpha).ker := sorry

/-- Exterior product by a fixed left cycle, descended through rational equivalence in the
right variable. -/
noncomputable def exteriorProductRight
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    RelativeChow δ Y m →+ RelativeChow δ (X ⨯ Y) (n + m - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance m)
    (exteriorProductClassRight δ h_delta X Y n m alpha)
    (boundaries_le_ker_exteriorProductClassRight δ h_delta X Y n m alpha)

/-- The right-descended Dedekind exterior product vanishes at a zero left cycle. -/
theorem exteriorProductRight_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    exteriorProductRight δ h_delta X Y n m 0 = 0 := sorry

/-- The right-descended Dedekind exterior product is additive in its left cycle. -/
theorem exteriorProductRight_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (alpha beta : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    exteriorProductRight δ h_delta X Y n m (alpha + beta) =
      exteriorProductRight δ h_delta X Y n m alpha +
        exteriorProductRight δ h_delta X Y n m beta := sorry

/-- Exterior product after descent in the right variable, as an additive map of left cycles. -/
noncomputable def exteriorProductFromCycles
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n →+
      RelativeChow δ Y m →+ RelativeChow δ (X ⨯ Y) (n + m - 1) where
  toFun := exteriorProductRight δ h_delta X Y n m
  map_zero' := exteriorProductRight_zero δ h_delta X Y n m
  map_add' := exteriorProductRight_add δ h_delta X Y n m

/-- The right-descended product kills rational boundaries in the left variable. -/
theorem boundaries_le_ker_exteriorProductFromCycles
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
      (exteriorProductFromCycles δ h_delta X Y n m).ker := sorry

/-- The degreewise Dedekind exterior product pairing on relative Chow groups. -/
noncomputable def exteriorProductPairing
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    RelativeChow δ X n →+ RelativeChow δ Y m →+
      RelativeChow δ (X ⨯ Y) (n + m - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance n)
    (exteriorProductFromCycles δ h_delta X Y n m)
    (boundaries_le_ker_exteriorProductFromCycles δ h_delta X Y n m)

/-- The Dedekind Chow pairing on two represented classes is represented by the concrete
cycle exterior product. -/
theorem exteriorProductPairing_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) m) :
    exteriorProductPairing δ h_delta X Y n m
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance n alpha)
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance m beta) =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction δ) inferInstance (n + m - 1)
        (CycleGroup.Dedekind.exteriorProductPairing δ h_delta X Y n m alpha beta) := sorry

/-- The Dedekind Chow exterior pairing is balanced over `ℤ`. -/
theorem exteriorProductPairing_zsmul
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m r : ℤ) (alpha : RelativeChow δ X n) (beta : RelativeChow δ Y m) :
    exteriorProductPairing δ h_delta X Y n m (r • alpha) beta =
      exteriorProductPairing δ h_delta X Y n m alpha (r • beta) := sorry

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
      (exteriorProductPairing δ h_delta X Y n m)
      (exteriorProductPairing_zsmul δ h_delta X Y n m)).toIntLinearMap

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
      exteriorProductPairing δ h_delta X Y n m alpha beta := sorry

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
        (CycleGroup.Dedekind.exteriorProductPairing δ h_delta X Y n m alpha beta) := sorry

end ChowGroup.Dedekind

end AlgebraicGeometry
