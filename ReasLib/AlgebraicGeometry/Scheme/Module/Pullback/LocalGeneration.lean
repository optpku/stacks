module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site

/-!
# Local generation of pulled-back scheme modules

Pullback along a morphism of schemes preserves finite type for module sheaves. This scheme-level
instance bridges the bundled scheme-module pullback functor to the generic ringed-site result.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a morphism of schemes preserves finite type for module sheaves. -/
instance pullback_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : Y.Modules)
    [ℱ.IsFiniteType] :
    ((Scheme.Modules.pullback f).obj ℱ).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.Modules
