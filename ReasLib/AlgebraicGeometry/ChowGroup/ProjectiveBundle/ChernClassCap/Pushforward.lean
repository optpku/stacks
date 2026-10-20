/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Intrinsic
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Proper pushforward commutes with every intrinsic Chern-class cap component of a
finite locally free module on the target. -/
theorem map_chernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) [IsProper p.left] (E : Y.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k)
    (cX : ChernClassCap δ X.hom ((Scheme.Modules.pullback p.left).obj E) r k α)
    (cY : ChernClassCap δ Y.hom E r k
      (CycleGroup.mapHom p.left (X.hom.relativeDimensionFunction δ)
        (Y.hom.relativeDimensionFunction δ) k α))
    (j : ℕ) :
    ChowGroup.map δ X Y p (k - (j : ℕ)) (cX.component j) = cY.component j := sorry

end AlgebraicGeometry.ChowGroup
