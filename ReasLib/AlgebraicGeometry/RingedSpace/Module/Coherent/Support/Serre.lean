module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.Support
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support.WeakSerre

/-!
# Serre classes of coherent module sheaves with prescribed support

This file records the Serre property for coherent module sheaves whose set-theoretic support is
contained in a prescribed subset.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Coh

/-- Coherent module sheaves supported on `T` form a Serre class. -/
instance supportedOnIsSerreClass {X : RingedSpace.{u}} (T : Set X) :
    (supportedOn T).IsSerreClass := sorry

end AlgebraicGeometry.RingedSpace.Coh
