/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Definition_71_9_2_RelativeEffectiveCartier
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

/-!
# Pullback along a relative effective Cartier divisor

On good algebraic spaces, a flat morphism of relative dimension `r` restricts
along a relative effective Cartier divisor `D` to an associated-cycle pullback
of degree `n + r - 1` on the zero scheme of `(O_X(D), 1_D)`.
-/

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
    ((ClosedSubspace.pointClosure y).inverseImage
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ p))
    (relativeDimensionFunction
      (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ)
    (n + (r : ℤ) - 1)

/-- The generator is the associated cycle of the inverse image of the reduced
point closure. -/
theorem relativeCartierPullbackGenerator_eq {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) (y : Points Y) :
    relativeCartierPullbackGenerator pY pX δ p r hp D n y =
      @ClosedSubspace.associatedCycle S
        (zeroScheme D.associatedSheaf D.canonicalSection).X
        (LocallyOfFiniteType.isLocallyNoetherian
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX))
        ((ClosedSubspace.pointClosure y).inverseImage
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ p))
        (relativeDimensionFunction
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX) δ)
        (n + (r : ℤ) - 1) :=
  sorry

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
  sorry

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
  map_zero' := sorry
  map_add' := sorry

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
  sorry

/-- Relative Cartier pullback of the zero cycle is zero. -/
theorem relativeCartierPullback_zero {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) (r : ℕ) [Flat p] [RelativeDimension p r]
    (hp : p ≫ pY = pX) (D : ClosedSubspace X)
    [IsRelativeEffectiveCartierDivisor p D.ι] (n : ℤ) :
    relativeCartierPullback pY pX δ p r hp D n 0 = 0 :=
  sorry

/-- The associated cycle of an integral closed subspace of `δ`-dimension `n` is
an `n`-cycle. -/
theorem associatedCycle_mem_cycleGroup {S : Scheme.{u}}
    {B Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (W : ClosedSubspace Y) (n : ℤ)
    (hW : closedSubspaceDeltaDimension pY δ W = (n : EInt)) :
    @ClosedSubspace.associatedCycle S Y
        (LocallyOfFiniteType.isLocallyNoetherian pY) W
        (relativeDimensionFunction pY δ) n ∈
      cycleGroup pY δ n :=
  sorry

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
          associatedCycle_mem_cycleGroup pY δ W n hW⟩ :
        Function.locallyFinsupp
          (Points (zeroScheme D.associatedSheaf D.canonicalSection).X) ℤ) =
      @ClosedSubspace.associatedCycle S
        (zeroScheme D.associatedSheaf D.canonicalSection).X
        (LocallyOfFiniteType.isLocallyNoetherian
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ pX))
        (W.inverseImage
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
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
