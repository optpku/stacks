/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle.ProperPushforward
import StacksCheckRecall

/-!
# Proper pushforward of associated cycles

In Situation 82.2.1, proper pushforward commutes with degree-`k` associated
cycles of closed subspaces and coherent modules with the stated dimension bounds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.8.3 (1): Proper pushforward commutes with the degree-`k` associated
cycle of a closed subspace of `δ`-dimension at most `k`. -/
@[stacks 0EP3] #check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_closedSubspaceCycle :
  ∀
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (Z : ClosedSubspace X)
    (hZ : closedSubspaceDeltaDimension pX δ Z ≤ (k : EInt)),
    properPushforwardCycle pX pY δ f hf (closedSubspaceCycle pX δ Z k hZ) =
      @moduleCycle S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj (Modules.pushforwardStructureModule Z.ι))
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) (Modules.pushforwardStructureModule Z.ι)
          (@Modules.ClosedImmersion.pushforward_unit_isCoherent S Z.X X
            (LocallyOfFiniteType.isLocallyNoetherian pX) Z.ι Z.isClosedImmersion)) k
        (moduleSupportDeltaDimension_pushforward_closedSubspace_le pX pY δ f hf k Z hZ))

/- Lemma 82.8.3 (2): Proper pushforward commutes with the degree-`k` associated
cycle of a coherent module whose support has `δ`-dimension at most `k`. -/
@[stacks 0EP3] #check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_moduleCycle :
  ∀
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pX δ F ≤ (k : EInt)),
    properPushforwardCycle pX pY δ f hf (moduleCycle pX δ F k hF) =
      @moduleCycle S B Y _ _ pY _ _ δ _ ((Modules.pushforward f).obj F)
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) F _) k
        (moduleSupportDeltaDimension_pushforward_le pX pY δ f hf k F hF))

