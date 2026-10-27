/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.PointClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback

/-! # Relative Cartier pullback on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The associated cycle of `Z(s) ∩ p⁻¹(closure({y}))` in degree `n + r - 1`,
where `s = 1_D`. -/
noncomputable def relativeCartierPullbackGenerator {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) (y : Points Y) :
    Function.locallyFinsupp
      (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ :=
  let _ := hp
  @ClosedSubspace.associatedCycle S
    (zeroScheme D.associatedSheaf D.canonicalSection).X
    (LocallyOfFiniteType.isLocallyNoetherian
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX))
    ((ClosedSubspace.pointClosure y).inverseImageSubspace
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ p))
    (relativeDimensionFunction
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ)
    (n + (r : ℤ) - 1)

/-- Coefficients of relative Cartier pullback are locally finite on `|Z(s)|`. -/
theorem relativeCartierPullback_locallyFiniteSupport {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : Function.locallyFinsupp (Points Y) ℤ) :
    LocallyFiniteSupport fun x :
        Points (zeroScheme D.associatedSheaf D.canonicalSection).X ↦
      ∑ᶠ y : Points Y,
        α y * relativeCartierPullbackGenerator pY pX δ p r hp D n y x :=
  sorry

/-- Coefficientwise pullback of a cycle along the restriction of a flat morphism
to a relative effective Cartier divisor. -/
noncomputable def relativeCartierPullbackCycle {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp
      (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ where
  toFun x :=
    ∑ᶠ y : Points Y,
      α y * relativeCartierPullbackGenerator pY pX δ p r hp D n y x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    relativeCartierPullback_locallyFiniteSupport pY pX δ p r hp D n α x

/-- The coefficient of a relative Cartier pullback is the locally finite sum of
input coefficients times associated cycles of inverse images of point closures. -/
theorem relativeCartierPullbackCycle_apply {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : Function.locallyFinsupp (Points Y) ℤ)
    (x : Points (zeroScheme D.associatedSheaf D.canonicalSection).X) :
    relativeCartierPullbackCycle pY pX δ p r hp D n α x =
      ∑ᶠ y : Points Y,
        α y * relativeCartierPullbackGenerator pY pX δ p r hp D n y x :=
  rfl

private theorem relativeCartierPullbackCycle_zero {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) :
    relativeCartierPullbackCycle pY pX δ p r hp D n 0 = 0 := by sorry

private theorem relativeCartierPullbackCycle_add {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α β : Function.locallyFinsupp (Points Y) ℤ) :
    relativeCartierPullbackCycle pY pX δ p r hp D n (α + β) =
      relativeCartierPullbackCycle pY pX δ p r hp D n α +
        relativeCartierPullbackCycle pY pX δ p r hp D n β := by sorry

/-- Relative Cartier pullback sends `n`-cycles on `Y` to `(n + r - 1)`-cycles on
the zero scheme of `(O_X(D), 1_D)`. -/
theorem relativeCartierPullback_mem {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ cycleGroup pY δ n) :
    relativeCartierPullbackCycle pY pX δ p r hp D n α ∈
      cycleGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1) :=
  sorry

/-- Cycle-level pullback along the restriction of a flat morphism of relative
dimension `r` to a relative effective Cartier divisor. -/
noncomputable def relativeCartierPullback {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) :
    cycleGroup pY δ n →+
      cycleGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1) where
  toFun α :=
    ⟨relativeCartierPullbackCycle pY pX δ p r hp D n α,
      relativeCartierPullback_mem pY pX δ p r hp D n α.property⟩
  map_zero' := by
    ext x
    change relativeCartierPullbackCycle pY pX δ p r hp D n 0 x = 0
    rw [relativeCartierPullbackCycle_zero pY pX δ p r hp D n]
    rfl
  map_add' := by
    intro α β
    ext x
    change relativeCartierPullbackCycle pY pX δ p r hp D n (α + β) x = _
    rw [relativeCartierPullbackCycle_add pY pX δ p r hp D n]
    change _ = (relativeCartierPullbackCycle pY pX δ p r hp D n (α : Function.locallyFinsupp (Points Y) ℤ) +
      relativeCartierPullbackCycle pY pX δ p r hp D n (β : Function.locallyFinsupp (Points Y) ℤ)) x
    rfl

/-- The additive pullback evaluates to the associated-cycle coefficient formula. -/
theorem relativeCartierPullback_apply {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : cycleGroup pY δ n)
    (x : Points (zeroScheme D.associatedSheaf D.canonicalSection).X) :
    (relativeCartierPullback pY pX δ p r hp D n α :
        Function.locallyFinsupp
          (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ) x =
      relativeCartierPullbackCycle pY pX δ p r hp D n α x :=
  rfl

/-- On the generator cycle of an integral closed subspace `W ⊂ Y` of
`δ`-dimension `n`, relative Cartier pullback is the associated cycle of
`Z(s) ∩ p⁻¹ W`. -/
theorem relativeCartierPullback_closedSubspace {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (W : ClosedSubspace Y) [IsIntegral W.X]
    (hW : closedSubspaceDeltaDimension pY δ W = (n : EInt)) :
    (relativeCartierPullback pY pX δ p r hp D n
        ⟨@ClosedSubspace.associatedCycle S Y
            (LocallyOfFiniteType.isLocallyNoetherian pY) W
            (relativeDimensionFunction pY δ) n,
          by
            rw [show @ClosedSubspace.associatedCycle S Y
              (LocallyOfFiniteType.isLocallyNoetherian pY) W
              (relativeDimensionFunction pY δ) n =
              closedSubspaceCycle pY δ W n (le_of_eq hW) by rfl]
            exact closedSubspaceCycle_mem_cycleGroup pY δ W n (le_of_eq hW)⟩ :
        Function.locallyFinsupp
          (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ) =
      @ClosedSubspace.associatedCycle S
        (zeroScheme D.associatedSheaf D.canonicalSection).X
        (LocallyOfFiniteType.isLocallyNoetherian
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX))
        (W.inverseImageSubspace
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ p))
        (relativeDimensionFunction
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ)
        (n + (r : ℤ) - 1) :=
  sorry

/-- Relative Cartier pullback sends rational boundaries to rational boundaries. -/
theorem relativeCartierPullback_mem_boundaries {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) :
    RationalEquivalence.boundaries pY δ n ≤
      (RationalEquivalence.boundaries
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
          (n + (r : ℤ) - 1)).comap
        (relativeCartierPullback pY pX δ p r hp D n) :=
  sorry

/-- Chow-level pullback along the restriction of a flat morphism of relative
dimension `r` to a relative effective Cartier divisor. -/
noncomputable def chowRelativeCartierPullback {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) :
    chowGroup pY δ n →+
      chowGroup (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1) :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pY δ n)
    (RationalEquivalence.boundaries
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
      (n + (r : ℤ) - 1))
    (relativeCartierPullback pY pX δ p r hp D n)
    (relativeCartierPullback_mem_boundaries pY pX δ p r hp D n)

/-- Relative Cartier pullback of a Chow class is induced by the cycle-level
map. -/
theorem chowRelativeCartierPullback_chowMk {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ)
    (α : cycleGroup pY δ n) :
    chowRelativeCartierPullback pY pX δ p r hp D n (chowMk pY δ n α) =
      chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (n + (r : ℤ) - 1)
        (relativeCartierPullback pY pX δ p r hp D n α) :=
  rfl

/-- For a flat morphism of relative dimension `r` and a relative effective
Cartier divisor, Gysin of the flat pullback of a cycle agrees with the Chow class
of its relative Cartier pullback. -/
theorem gysin_flatPullback_eq_relativeCartierPullback {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    gysin pX δ (k + (r : ℤ)) D.associatedSheaf D.canonicalSection
        (add_right_comm k 1 (r : ℤ) ▸
          flatPullbackHom pY pX δ p r hp (k + 1) α) =
      chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
        (k + (r : ℤ))
        (((congrArg (fun z : ℤ ↦ z - 1)
              (add_right_comm k 1 (r : ℤ))).trans
            (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
          relativeCartierPullback pY pX δ p r hp D (k + 1) α) :=
  sorry

/-- First-Chern cap of the flat pullback of a cycle is the closed pushforward of
its relative Cartier pullback, for a flat morphism and a relative effective
Cartier divisor. -/
theorem firstChernClassCap_flatPullback_eq_pushforward_relativeCartierPullback
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι]
    (k : ℤ) (α : cycleGroup pY δ (k + 1)) :
    firstChernClassCap pX δ D.associatedSheaf (k + (r : ℤ))
        (add_right_comm k 1 (r : ℤ) ▸
          flatPullbackHom pY pX δ p r hp (k + 1) α) =
      chowPushforward pX δ
        (zeroScheme D.associatedSheaf D.canonicalSection) (k + (r : ℤ))
        (chowMk (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ
          (k + (r : ℤ))
          (((congrArg (fun z : ℤ ↦ z - 1)
                (add_right_comm k 1 (r : ℤ))).trans
              (Int.add_sub_cancel (k + (r : ℤ)) 1)) ▸
            relativeCartierPullback pY pX δ p r hp D (k + 1) α)) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom
