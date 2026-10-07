module

public import ReasLib.AlgebraicGeometry.ChowGroup.ClosedCover
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Components

/-!
# First Chern classes and closed subschemes

This file identifies the first-Chern cap class of a closed subscheme with the pushforward
of the zero-cycle class of a generically regular section on that subscheme.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a closed subscheme, capping its cycle with the first Chern class of an invertible
module gives the pushforward of the zero-cycle class of a generically regular restricted
section, under the corresponding dimension bounds. -/
theorem firstChernClassCap_closedSubscheme_eq_zeroCycleClass
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (Y : X.IdealSheafData) (s : ((pullback Y.subschemeι).obj ℒ).sections) (k : ℤ)
    (hY : p.closedSubschemeDeltaDimension δ Y ≤ ((k + 1 : ℤ) : EInt))
    (hZ : (Y.subschemeι ≫ p).closedSubschemeDeltaDimension δ
      (zeroIdealSheaf ((pullback Y.subschemeι).obj ℒ) s) ≤ (k : EInt))
    (hregular : ∀ ξ : genericPoints (zeroScheme ((pullback Y.subschemeι).obj ℒ) s),
      (Y.subschemeι ≫ p).relativeDimensionFunction δ
          (zeroSchemeι ((pullback Y.subschemeι).obj ℒ) s ξ.1) = k →
        RingedSpace.IsRegularSectionAt ((pullback Y.subschemeι).obj ℒ) s
          (zeroSchemeι ((pullback Y.subschemeι).obj ℒ) s ξ.1)) :
    firstChernClassCap p δ ℒ k (p.closedSubschemeCycle δ Y (k + 1) hY) =
      ChowGroup.map δ (Over.mk (Y.subschemeι ≫ p)) (Over.mk p)
        (Over.homMk Y.subschemeι rfl : Over.mk (Y.subschemeι ≫ p) ⟶ Over.mk p) k
        (@chowClass Y.subscheme
          (LocallyOfFiniteType.isLocallyNoetherian (Y.subschemeι ≫ p))
          ((Y.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k
          (relativeZeroCycleGroup (Y.subschemeι ≫ p) δ
            ((pullback Y.subschemeι).obj ℒ) s k)) := sorry

end AlgebraicGeometry.Scheme.Modules
