module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.24.3: flat pullback commutes with intersecting the fundamental cycle by the
first Chern class of an invertible module. -/
@[stacks 02SM] #check
  (AlgebraicGeometry.ChowGroup.flatPullback_firstChernClassCap_fundamental :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) (r : ℕ)
      [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] (k : ℤ)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
      (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ],
      flatPullback δ X Y f r k
          (Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
            (@CycleGroup.fundamental Y.left
              (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
              (Y.hom.relativeDimensionFunction δ) (k + 1))) =
        Scheme.Modules.firstChernClassCap X.hom δ
          ((Scheme.Modules.pullback f.left).obj ℒ) (k + (r : ℤ))
          (@CycleGroup.fundamental X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) (k + (r : ℤ) + 1)))

end AlgebraicGeometry.ChowGroup
