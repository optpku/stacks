/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Flat pullback of associated cycles on algebraic spaces

Flat pullback shifts dimension bounds and commutes with the associated cycles
of closed subspaces and coherent modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Flat inverse image under a morphism of relative dimension `r` raises the
`δ`-dimension bound of a closed subspace by at most `r`. -/
@[stacks 0EPB]
theorem closedSubspaceDeltaDimension_inverseImage_le {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)) :
    closedSubspaceDeltaDimension pX δ (Z.inverseImageSubspace f) ≤
      (k + (r : ℤ) : EInt) :=
  sorry

/-- The associated cycle of the inverse image of a closed subspace is the flat
pullback of its associated cycle, in the degree shifted by the relative dimension. -/
@[stacks 0EPB]
theorem flatPullback_closedSubspaceCycle {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)) :
    @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian pX)
        (Z.inverseImageSubspace f) (relativeDimensionFunction pX δ) (k + (r : ℤ)) =
      flatPullback pY pX δ f r hf k
        (@ClosedSubspace.associatedCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          (relativeDimensionFunction pY δ) k) :=
  sorry

/-- Pullback along a flat morphism of relative dimension `r` raises the
`δ`-dimension bound of coherent support by at most `r`. -/
@[stacks 0EPB]
theorem moduleSupportDeltaDimension_pullback_le {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _) ≤
      (k + (r : ℤ) : EInt) :=
  sorry

/-- Flat pullback carries the associated cycle of a coherent module to the
associated cycle of its pullback, in the degree shifted by the relative dimension. -/
@[stacks 0EPB]
theorem flatPullback_moduleCycle {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)) :
    flatPullback pY pX δ f r hf k (moduleCycle pY δ F k hF) =
      @moduleCycle S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _)
        (k + (r : ℤ))
        (moduleSupportDeltaDimension_pullback_le pY pX δ f r hf k F hF) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
