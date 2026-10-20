/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.RelativeDimension

/-!
# Push-pull of cycles along finite locally free morphisms

For a finite locally free morphism of rank `d` of good algebraic spaces, the
composite of flat pullback of relative dimension `0` with proper pushforward
acts on `k`-cycles by multiplication by `d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- For a finite locally free morphism of rank `d`, the composite of flat
pullback of relative dimension `0` with proper pushforward multiplies every
`k`-cycle by `d`. -/
theorem properPushforward_flatPullback_nsmul {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (d : ℕ) [FiniteLocallyFreeOfRank f d]
    (hf : f ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ cycleGroup pY δ k) :
    properPushforwardCycle pX pY δ f hf
        (flatPullback pY pX δ f 0 hf k α) =
      d • α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
