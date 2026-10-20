module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.PointClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension

/-!
# Flat pullback of cycles on algebraic spaces

Flat pullback is the locally finite sum of associated cycles of scheme-theoretic
inverse images of reduced point closures, weighted by the input coefficients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Coefficients of a flat pullback are locally finite on `|X|`. -/
theorem flatPullback_locallyFiniteSupport {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
            ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) x) :=
  sorry

/-- Flat pullback of a cycle along a morphism of relative dimension `r`, as a
locally finite integer combination of associated cycles of inverse images of
reduced point closures. -/
def flatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun x :=
    ∑ᶠ y : Points Y,
      α y *
        (@ClosedSubspace.associatedCycle S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
          ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) x)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    flatPullback_locallyFiniteSupport pY pX δ f r hf k α x

/-- The coefficient of a flat pullback is the locally finite sum of input
coefficients times associated cycles of inverse images of point closures. -/
theorem flatPullback_apply {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ)
    (x : Points X) :
    flatPullback pY pX δ f r hf k α x =
      ∑ᶠ y : Points Y,
        α y *
          (@ClosedSubspace.associatedCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
            ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) x) :=
  sorry

/-- Flat pullback sends `k`-cycles on `Y` to `(k + r)`-cycles on `X`. -/
theorem flatPullback_mem_cycleGroup {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ (cycleGroup pY) δ k) :
    flatPullback pY pX δ f r hf k α ∈ (cycleGroup pX) δ (k + (r : ℤ)) :=
  sorry

/-- Flat pullback sends the zero cycle to zero. -/
theorem flatPullback_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    flatPullback pY pX δ f r hf k (0 : Function.locallyFinsupp (Points Y) ℤ) =
      0 :=
  sorry

/-- Flat pullback preserves addition of cycles. -/
theorem flatPullback_add {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ)
    (α β : Function.locallyFinsupp (Points Y) ℤ) :
    flatPullback pY pX δ f r hf k (α + β) =
      flatPullback pY pX δ f r hf k α + flatPullback pY pX δ f r hf k β :=
  sorry

/-- Flat pullback as an additive map `Z_k(Y) → Z_{k + r}(X)`. -/
def flatPullbackHom {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    (cycleGroup pY) δ k →+ (cycleGroup pX) δ (k + (r : ℤ)) where
  toFun α :=
    ⟨flatPullback pY pX δ f r hf k α,
      flatPullback_mem_cycleGroup pY pX δ f r hf k α.property⟩
  map_zero' := by
    apply Subtype.ext
    exact flatPullback_zero pY pX δ f r hf k
  map_add' α β := by
    apply Subtype.ext
    exact flatPullback_add pY pX δ f r hf k α β

/-- Flat pullback of the generator cycle of an integral closed subspace `Z` of
`δ`-dimension `k` is the associated `(k + r)`-cycle of the scheme-theoretic
inverse image. -/
theorem flatPullback_integral {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y) [IsIntegral Z.X]
    (hZ : (closedSubspaceDeltaDimension pY) δ Z = (k : EInt)) :
    flatPullback pY pX δ f r hf k
        (@ClosedSubspace.associatedCycle S Y
          (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          ((relativeDimensionFunction pY) δ) k) =
      @ClosedSubspace.associatedCycle S X
        (LocallyOfFiniteType.isLocallyNoetherian pX) (Z.inverseImageSubspace f)
        ((relativeDimensionFunction pX) δ) (k + (r : ℤ)) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
