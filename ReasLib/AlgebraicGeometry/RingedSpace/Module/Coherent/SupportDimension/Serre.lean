module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support.WeakSerre

/-!
# Serre classes of coherent sheaves with bounded support dimension

This file records the Serre property for coherent sheaves whose support is bounded with respect
to an integer-valued function.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Coh

/-- Coherent module sheaves supported where `d ≤ k` form a Serre class. -/
instance supportDimensionLEIsSerreClass {X : RingedSpace.{u}} (d : X → ℤ) (k : ℤ) :
    (supportDimensionLE d k).IsSerreClass := sorry

end AlgebraicGeometry.RingedSpace.Coh
