module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/- Lemma 42.38.5: Flat pullback by a morphism of relative dimension `r` commutes
with the `j`th Chern-class cap of a finite locally free module of rank `r`. -/
@[stacks 02U8] #check
  (AlgebraicGeometry.ChowGroup.ChernClassCap.flatPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (E : Y.left.Modules) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)
      (cY : ChernClassCap δ Y.hom E r k α)
      (cX : ChernClassCap δ X.hom ((Scheme.Modules.pullback f.left).obj E) r
        (k + (r : ℤ)) (CycleGroup.flatPullback δ X Y f r k α))
      (j : ℕ),
      @reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance
          ((k - (j : ℤ)) + (r : ℤ)) (k + (r : ℤ) - (j : ℤ))
          (sub_add_eq_add_sub k (j : ℤ) (r : ℤ))
          (ChowGroup.flatPullback δ X Y f r (k - (j : ℤ)) (cY.component j)) =
        cX.component j)

end AlgebraicGeometry.ChowGroup.ChernClassCap
