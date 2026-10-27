/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-! # Proper pushforward and refined Gysin homomorphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

/-- The canonical map of zero schemes obtained by pulling back a section
along a proper morphism is proper. -/
instance zeroSchemePullbackMap_proper {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) [Proper f] (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)] :
    Proper (zeroSchemePullbackMap f L s) :=
  Proper.of_isPullback (zeroSchemePullbackSquare f L s) inferInstance

end AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Refined Gysin commutes with proper pushforward of cycles and Chow classes
in the cartesian square of zero schemes of a section and its pullback. -/
theorem gysin_properPushforward {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) [Proper f] (hf : f ≫ pX = pX')
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α' : cycleGroup pX' δ (k + 1)) :
    gysin pX δ k L s (properPushforwardHom pX' pX δ f hf (k + 1) α') =
      ChowGroup.properPushforward
        (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) ≫ pX')
        (zeroSchemeι L s ≫ pX) δ (zeroSchemePullbackMap f L s)
        (by rw [← Category.assoc, zeroSchemePullbackMap_comp, Category.assoc, hf]) k
        (gysin pX' δ k ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) α') := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
