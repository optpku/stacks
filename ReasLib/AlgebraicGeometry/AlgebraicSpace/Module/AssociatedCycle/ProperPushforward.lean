/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle.ClosedSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Proper

/-!
# Proper pushforward of associated cycles

Proper pushforward commutes with associated cycles of coherent modules and
closed subspaces over an absolutely quasi-separated universally catenary base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The support of the ordinary pushforward of a coherent module along a proper
morphism over an absolutely quasi-separated universally catenary base has
`δ`-dimension at most `k` if the original support does. -/
theorem moduleSupportDeltaDimension_pushforward_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pX δ F ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj F)
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) F _) ≤ (k : EInt) := sorry

/-- For a closed subspace of `δ`-dimension at most `k`, the support of the proper
pushforward of its structure module has `δ`-dimension at most `k`. -/
theorem moduleSupportDeltaDimension_pushforward_closedSubspace_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (Z : ClosedSubspace X)
    (hZ : closedSubspaceDeltaDimension pX δ Z ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj (Modules.pushforwardStructureModule Z.ι))
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) (Modules.pushforwardStructureModule Z.ι)
          (@Modules.ClosedImmersion.pushforward_unit_isCoherent S Z.X X
            (LocallyOfFiniteType.isLocallyNoetherian pX) Z.ι Z.isClosedImmersion)) ≤ (k : EInt) := sorry

/-- Proper pushforward over an absolutely quasi-separated universally catenary
base commutes with the degree-`k` associated cycle of a coherent module whose
support has `δ`-dimension at most `k`. -/
theorem properPushforward_moduleCycle
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pX δ F ≤ (k : EInt)) :
    properPushforwardCycle pX pY δ f hf (moduleCycle pX δ F k hF) =
      @moduleCycle S B Y _ _ pY _ _ δ _ ((Modules.pushforward f).obj F)
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) F _) k
        (moduleSupportDeltaDimension_pushforward_le pX pY δ f hf k F hF) := sorry

/-- Proper pushforward of the degree-`k` cycle of a closed subspace of
`δ`-dimension at most `k` equals the degree-`k` associated cycle of the ordinary
pushforward of its structure module. -/
theorem properPushforward_closedSubspaceCycle
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (Z : ClosedSubspace X)
    (hZ : closedSubspaceDeltaDimension pX δ Z ≤ (k : EInt)) :
    properPushforwardCycle pX pY δ f hf (closedSubspaceCycle pX δ Z k hZ) =
      @moduleCycle S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj (Modules.pushforwardStructureModule Z.ι))
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) (Modules.pushforwardStructureModule Z.ι)
          (@Modules.ClosedImmersion.pushforward_unit_isCoherent S Z.X X
            (LocallyOfFiniteType.isLocallyNoetherian pX) Z.ι Z.isClosedImmersion)) k
        (moduleSupportDeltaDimension_pushforward_closedSubspace_le pX pY δ f hf k Z hZ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
