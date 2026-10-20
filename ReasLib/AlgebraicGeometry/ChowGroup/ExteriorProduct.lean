/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct

/-!
# Exterior products on Chow groups over a field

This file descends the cycle exterior product through rational equivalence and assembles the
degreewise pairings into an associative exterior product on total Chow homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace ChowGroup

/-- For a fixed cycle on `X`, take the Chow class of its cycle-level exterior product. -/
noncomputable def exteriorProductClassRight (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m →+
      @ChowGroup (X ⨯ Y).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m) :=
  (@chowClass (X ⨯ Y).left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m)).comp
    (CycleGroup.exteriorProductPairing X Y n m alpha)

/-- Taking the Chow class after cycle exterior product has the expected value. -/
theorem exteriorProductClassRight_apply (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductClassRight X Y n m alpha beta =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m)
        (CycleGroup.exteriorProductPairing X Y n m alpha beta) := sorry

/-- For a fixed left cycle, the exterior product kills rational boundaries in the right
variable. -/
theorem boundaries_le_ker_exteriorProductClassRight (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    @RationalEquivalence.boundaries Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m ≤
      (exteriorProductClassRight X Y n m alpha).ker := sorry

/-- Exterior product by a fixed left cycle, descended through rational equivalence in the
right variable. -/
noncomputable def exteriorProductRight (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    @ChowGroup Y.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ Y.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m →+
      @ChowGroup (X ⨯ Y).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries Y.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ Y.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m)
    (exteriorProductClassRight X Y n m alpha)
    (boundaries_le_ker_exteriorProductClassRight.{u, u} X Y n m alpha)

/-- The right-descended exterior product evaluates on a cycle class by the cycle pairing. -/
theorem exteriorProductRight_chowClass (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductRight X Y n m alpha
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m beta) =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m)
        (CycleGroup.exteriorProductPairing X Y n m alpha beta) := sorry

/-- The right-descended exterior product vanishes at a zero left cycle. -/
theorem exteriorProductRight_zero (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    exteriorProductRight X Y n m 0 = 0 := sorry

/-- The right-descended exterior product is additive in its left cycle. -/
theorem exteriorProductRight_add (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha beta : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    exteriorProductRight X Y n m (alpha + beta) =
      exteriorProductRight X Y n m alpha + exteriorProductRight X Y n m beta := sorry

/-- Exterior product after descent in the right variable, as an additive map of left cycles. -/
noncomputable def exteriorProductFromCycles (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n →+
      @ChowGroup Y.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ Y.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m →+
        @ChowGroup (X ⨯ Y).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m) where
  toFun := exteriorProductRight X Y n m
  map_zero' := exteriorProductRight_zero X Y n m
  map_add' := exteriorProductRight_add X Y n m

/-- The right-descended exterior product kills rational boundaries in the left variable. -/
theorem boundaries_le_ker_exteriorProductFromCycles (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    @RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n ≤
      (exteriorProductFromCycles X Y n m).ker := sorry

/-- The degreewise exterior product pairing on Chow groups over a field. -/
noncomputable def exteriorProductPairing (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    @ChowGroup X.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n →+
      @ChowGroup Y.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ Y.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m →+
        @ChowGroup (X ⨯ Y).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
    (exteriorProductFromCycles X Y n m)
    (boundaries_le_ker_exteriorProductFromCycles.{u, u} X Y n m)

/-- The Chow exterior pairing on two represented classes is represented by the cycle
exterior product. -/
theorem exteriorProductPairing_chowClass (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) m) :
    exteriorProductPairing X Y n m
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n alpha)
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m beta) =
      @chowClass (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m)
        (CycleGroup.exteriorProductPairing X Y n m alpha beta) := sorry

/-- The Chow exterior pairing is balanced over `ℤ`. -/
theorem exteriorProductPairing_zsmul (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) (r : ℤ)
    (alpha : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
    (beta : @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) :
    exteriorProductPairing X Y n m (r • alpha) beta =
      exteriorProductPairing X Y n m alpha (r • beta) := sorry

/-- The canonical degreewise exterior-product homomorphism on Chow groups over a field. -/
noncomputable def exteriorProduct (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ) :
    TensorProduct ℤ
        (@ChowGroup X.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
        (@ChowGroup Y.left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ Y.hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) →+
      @ChowGroup (X ⨯ Y).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m) :=
  TensorProduct.liftAddHom (exteriorProductPairing X Y n m)
    (exteriorProductPairing_zsmul.{u, u, u} X Y n m)

/-- The Chow exterior product evaluates on a pure tensor by the descended pairing. -/
theorem exteriorProduct_tmul (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
    (beta : @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) :
    exteriorProduct X Y n m (alpha ⊗ₜ[ℤ] beta) =
      exteriorProductPairing X Y n m alpha beta := sorry

/-- The Chow exterior-product homomorphism is determined by its values on pure tensors. -/
theorem exteriorProduct_unique (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (f : TensorProduct ℤ
      (@ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
      (@ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) →+
        @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (n + m))
    (h : ∀ alpha beta, f (alpha ⊗ₜ[ℤ] beta) =
      exteriorProductPairing X Y n m alpha beta) :
    f = exteriorProduct X Y n m := sorry

namespace Total

/-- The exterior product on total Chow homology over a field, assembled from the degreewise
exterior-product pairings. -/
noncomputable def exteriorProduct (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) Y →+
      Total (fun _ ↦ 0) (X ⨯ Y) :=
  DirectSum.toAddMonoid fun n ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun m ↦
      AddMonoidHom.flip <|
        (DirectSum.of (fun d : ℤ ↦
          @ChowGroup (X ⨯ Y).left
            (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance
              (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
                (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
            ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d)
          (n + m)).compHom.comp (ChowGroup.exteriorProductPairing X Y n m)

/-- The total Chow exterior product of homogeneous classes is the homogeneous degreewise
exterior product in degree `n + m`. -/
theorem exteriorProduct_of (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ)
    (alpha : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n)
    (beta : @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) :
    exteriorProduct X Y
        (DirectSum.of (fun d : ℤ ↦
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d) n alpha)
        (DirectSum.of (fun d : ℤ ↦
          @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d) m beta) =
      DirectSum.of (fun d : ℤ ↦
        @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance d) (n + m)
            (ChowGroup.exteriorProductPairing X Y n m alpha beta) := sorry

/-- Passage from total cycles to total Chow classes commutes with the exterior product. -/
theorem exteriorProduct_chowClass (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (alpha : CycleGroup.Total (fun _ ↦ 0) X)
    (beta : CycleGroup.Total (fun _ ↦ 0) Y) :
    chowClass (fun _ ↦ 0) (X ⨯ Y)
        (CycleGroup.Total.exteriorProduct X Y alpha beta) =
      exteriorProduct X Y (chowClass (fun _ ↦ 0) X alpha)
        (chowClass (fun _ ↦ 0) Y beta) := sorry

end Total

/-- Associativity descends from total cycles to total Chow homology and uses the canonical
proper pushforward along the product associator. -/
theorem exteriorProduct_assoc_of_cycle
    {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (cycleExteriorProduct : ∀ {A B : Over S} [LocallyOfFiniteType A.hom]
      [LocallyOfFiniteType B.hom],
      CycleGroup.Total delta A →+ CycleGroup.Total delta B →+
        CycleGroup.Total delta (A ⨯ B))
    (exteriorProduct : ∀ {A B : Over S} [LocallyOfFiniteType A.hom]
      [LocallyOfFiniteType B.hom],
      ChowGroup.Total delta A →+ ChowGroup.Total delta B →+
        ChowGroup.Total delta (A ⨯ B))
    (h_product : ∀ {A B : Over S} [LocallyOfFiniteType A.hom]
      [LocallyOfFiniteType B.hom] (a : CycleGroup.Total delta A)
      (b : CycleGroup.Total delta B),
      Total.chowClass delta (A ⨯ B) (cycleExteriorProduct a b) =
        exteriorProduct (Total.chowClass delta A a) (Total.chowClass delta B b))
    (h_cycle_assoc : ∀ (a : CycleGroup.Total delta X) (b : CycleGroup.Total delta Y)
      (c : CycleGroup.Total delta Z),
      CycleGroup.Total.map delta (Limits.prod.associator X Y Z).hom
          (cycleExteriorProduct (cycleExteriorProduct a b) c) =
        cycleExteriorProduct a (cycleExteriorProduct b c))
    (alpha : ChowGroup.Total delta X) (beta : ChowGroup.Total delta Y)
    (gamma : ChowGroup.Total delta Z) :
    Total.map delta (Limits.prod.associator X Y Z).hom
        (exteriorProduct (exteriorProduct alpha beta) gamma) =
      exteriorProduct alpha (exteriorProduct beta gamma) := sorry

namespace Total

/-- The exterior product on total Chow homology over a field is associative after pushforward
along the canonical associator from `(X ⨯ Y) ⨯ Z` to `X ⨯ (Y ⨯ Z)`. -/
theorem exteriorProduct_assoc {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (alpha : Total (fun _ ↦ 0) X) (beta : Total (fun _ ↦ 0) Y)
    (gamma : Total (fun _ ↦ 0) Z) :
    map (fun _ ↦ 0) (Limits.prod.associator X Y Z).hom
        (exteriorProduct (X ⨯ Y) Z (exteriorProduct X Y alpha beta) gamma) =
      exteriorProduct X (Y ⨯ Z) alpha (exteriorProduct Y Z beta gamma) := sorry

end Total

end ChowGroup

end AlgebraicGeometry
