module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.AssociatedCycle
import StacksCheckRecall

/-!
# Flat pullback of associated cycles

In Situation 82.2.1, for good `X`, `Y / B` and a flat morphism `f : X ⟶ Y` of
relative dimension `r`, inverse images of closed subspaces and pullbacks of
coherent modules increase `δ`-dimension by at most `r`, and their associated
cycles are compatible with flat pullback.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.10.5: Flat inverse images and coherent pullbacks satisfy the
shifted dimension bounds and associated-cycle identities. -/
@[stacks 0EPB] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension_inverseImage_le :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)),
    closedSubspaceDeltaDimension pX δ (Z.inverseImageSubspace f) ≤
      (k + (r : ℤ) : EInt))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_closedSubspaceCycle :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)),
    @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian pX)
        (Z.inverseImageSubspace f) (relativeDimensionFunction pX δ) (k + (r : ℤ)) =
      flatPullback pY pX δ f r hf k
        (@ClosedSubspace.associatedCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          (relativeDimensionFunction pY δ) k))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.moduleSupportDeltaDimension_pullback_le :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)),
    @moduleSupportDeltaDimension S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _) ≤
      (k + (r : ℤ) : EInt))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_moduleCycle :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)),
    flatPullback pY pX δ f r hf k (moduleCycle pY δ F k hF) =
      @moduleCycle S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _)
        (k + (r : ℤ))
        (moduleSupportDeltaDimension_pullback_le pY pX δ f r hf k F hF))
