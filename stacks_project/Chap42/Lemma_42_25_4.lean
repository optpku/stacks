module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.ClosedSubscheme

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.25.4: for a closed subscheme `Y` of `X`, the first Chern class of an
invertible module capped with the degree-`k + 1` cycle of `Y` is the degree-`k` Chow class
of the zero scheme of a generically regular section on `Y`, pushed forward to `X`. -/
@[stacks 02SQ] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_closedSubscheme_eq_zeroCycleClass :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
      (Y : X.IdealSheafData) (s : ((pullback Y.subschemeι).obj ℒ).sections) (k : ℤ)
      (hY : p.closedSubschemeDeltaDimension δ Y ≤ ((k + 1 : ℤ) : EInt))
      (hZ : (Y.subschemeι ≫ p).closedSubschemeDeltaDimension δ
        (zeroIdealSheaf ((pullback Y.subschemeι).obj ℒ) s) ≤ (k : EInt))
      (hregular : ∀ ξ : genericPoints (zeroScheme ((pullback Y.subschemeι).obj ℒ) s),
        (Y.subschemeι ≫ p).relativeDimensionFunction δ
            (zeroSchemeι ((pullback Y.subschemeι).obj ℒ) s ξ.1) = k →
          RingedSpace.IsRegularSectionAt ((pullback Y.subschemeι).obj ℒ) s
            (zeroSchemeι ((pullback Y.subschemeι).obj ℒ) s ξ.1)),
      firstChernClassCap p δ ℒ k (p.closedSubschemeCycle δ Y (k + 1) hY) =
        ChowGroup.map δ (Over.mk (Y.subschemeι ≫ p)) (Over.mk p)
          (Over.homMk Y.subschemeι rfl : Over.mk (Y.subschemeι ≫ p) ⟶ Over.mk p) k
          (@chowClass Y.subscheme
            (LocallyOfFiniteType.isLocallyNoetherian (Y.subschemeι ≫ p))
            ((Y.subschemeι ≫ p).relativeDimensionFunction δ) inferInstance k
            (relativeZeroCycleGroup (Y.subschemeι ≫ p) δ
              ((pullback Y.subschemeι).obj ℒ) s k)))

end AlgebraicGeometry.Scheme.Modules
