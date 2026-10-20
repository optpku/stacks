module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic

/-!
# Finite local rank for locally ringed space modules

This leaf records the fixed-rank pullback API for modules over locally ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

/-- Pullback along a morphism of locally ringed spaces preserves finite local freeness of rank one. -/
instance pullback_isFiniteLocallyFreeOfRank_one
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u} 1 L] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u} 1
      ((RingedSpace.Hom.pullback f.toShHom).obj L) := sorry

end AlgebraicGeometry.LocallyRingedSpace.Modules
