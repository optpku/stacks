module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocallyFree
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.BoundedAbove
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.Pullback

/-!
# Pullback of locally bounded finite locally free representatives

Derived pullback preserves the existence of a global cochain-complex representative which is
locally bounded in both directions and termwise finite locally free.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- A derived pullback of a module admitting a locally bounded finite locally free representative
again admits such a representative. -/
theorem modulePullbackDerived_hasLocallyBoundedFiniteLocallyFreeRepresentative
    (f : X ⟶ Y) (M : ModuleDerived Y)
    (hrep : ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative M) :
    ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((modulePullbackDerived f).obj M) := sorry

end AlgebraicGeometry.RingedSpace
