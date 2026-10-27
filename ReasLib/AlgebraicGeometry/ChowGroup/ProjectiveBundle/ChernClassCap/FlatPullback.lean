/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Intrinsic
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/-- Flat pullback by a morphism of relative dimension `e` commutes with the `j`th
Chern-class cap of a finite locally free module of rank `r`. -/
theorem flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r e : ℕ) [Flat f.left]
    [Scheme.Hom.RelativeDimension f.left e]
    (E : Y.left.Modules) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)
    (cY : ChernClassCap δ Y.hom E r k α)
    (cX : ChernClassCap δ X.hom ((Scheme.Modules.pullback f.left).obj E) r
      (k + (e : ℤ)) (CycleGroup.flatPullback δ X Y f e k α))
    (j : ℕ) :
    @reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance
        ((k - (j : ℤ)) + (e : ℤ)) (k + (e : ℤ) - (j : ℤ))
        (sub_add_eq_add_sub k (j : ℤ) (e : ℤ))
        (ChowGroup.flatPullback δ X Y f e (k - (j : ℤ)) (cY.component j)) =
      cX.component j := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap
