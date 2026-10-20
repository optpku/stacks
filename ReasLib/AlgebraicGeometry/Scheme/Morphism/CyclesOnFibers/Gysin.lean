/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback.FiniteType

/-!
# Compatibility of the fibre-cycle action with Gysin maps

The action of a relative cycle commutes with the cycle-level Gysin maps of an
invertible module whose restriction to the zero scheme of its section is trivial.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme (Modules)
open AlgebraicGeometry.Scheme.Modules hiding pullback

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (f : X ⟶ Y) [LocallyOfFiniteType f.left] [IsLocallyNoetherian Y.left]
variable (ℒ : Y.left.Modules) [Invertible ℒ] (s : ℒ.sections)

/-- The action of a relative nonnegative-dimensional fibre cycle commutes with
cycle-level Gysin along the cartesian zero-scheme square of a section of an invertible
module whose restriction to its zero scheme is trivial. -/
theorem cap_trivialGysin
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : RelativeCycle.IsRelative α)
    (htriv : RingedSpace.IsTrivial ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ))
    (e : ℤ) (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) (e + 1)) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ((Modules.pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫
          f.left ≫ Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (trivialGysin (f.left ≫ Y.hom) δ ((Modules.pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) ((r : ℤ) + e)
          (CycleGroup.reindex ((f.left ≫ Y.hom).relativeDimensionFunction δ)
            (add_assoc (r : ℤ) e 1).symm (cap Y.hom f.left δ α β))) =
      CycleGroup.toAlgebraicCycle
        ((zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s) ≫ zeroSchemeι ℒ s ≫
          Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap (zeroSchemeι ℒ s ≫ Y.hom) (zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s)) δ
          (FiberCycleFamily.baseChange (zeroSchemePullbackSquare f.left ℒ s) α)
          (trivialGysin Y.hom δ ℒ s htriv e β)) :=
  sorry

/-- The coefficients of the Gysin image of a relative-cycle action equal those of
the action of the base-changed relative cycle on the Gysin image. -/
theorem cap_trivialGysin_apply
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : RelativeCycle.IsRelative α)
    (htriv : RingedSpace.IsTrivial ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ))
    (e : ℤ) (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) (e + 1))
    (z : zeroScheme ((Modules.pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s)) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ((Modules.pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫
          f.left ≫ Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (trivialGysin (f.left ≫ Y.hom) δ ((Modules.pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) ((r : ℤ) + e)
          (CycleGroup.reindex ((f.left ≫ Y.hom).relativeDimensionFunction δ)
            (add_assoc (r : ℤ) e 1).symm (cap Y.hom f.left δ α β))) z =
      CycleGroup.toAlgebraicCycle
        ((zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s) ≫ zeroSchemeι ℒ s ≫
          Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap (zeroSchemeι ℒ s ≫ Y.hom) (zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s)) δ
          (FiberCycleFamily.baseChange (zeroSchemePullbackSquare f.left ℒ s) α)
          (trivialGysin Y.hom δ ℒ s htriv e β)) z :=
  congrArg (fun γ : AlgebraicCycle _ ℤ => γ z)
    (cap_trivialGysin δ f ℒ s r α hα htriv e β)

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
