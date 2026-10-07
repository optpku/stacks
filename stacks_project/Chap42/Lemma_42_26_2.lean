module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.26.2: flat pullback commutes with intersection by the first Chern class of an
invertible module. -/
@[stacks 02SS]
#check (AlgebraicGeometry.ChowGroup.flatPullback_firstChernClassCap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k),
    @reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance
        ((k - 1) + (r : ℤ)) (k + (r : ℤ) - 1) (CycleGroup.flatDivisorDegree k r)
        (flatPullback δ X Y f r (k - 1)
          (Scheme.Modules.firstChernClassCap Y.hom δ ℒ (k - 1)
            (CycleGroup.reindex (Y.hom.relativeDimensionFunction δ)
              (sub_add_cancel k 1).symm α))) =
      Scheme.Modules.firstChernClassCap X.hom δ
        ((Scheme.Modules.pullback f.left).obj ℒ) (k + (r : ℤ) - 1)
        (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel (k + (r : ℤ)) 1).symm
          (CycleGroup.flatPullback δ X Y f r k α)))

end AlgebraicGeometry.ChowGroup
