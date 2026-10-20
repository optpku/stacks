module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of injective module sheaves

This leaf specializes the site-level restriction-surjectivity theorem to inclusions of open
subsets of a ringed space.  Both the module-sheaf and underlying additive-sheaf presentations are
kept as named entry points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}} {V U : Opens X.carrier}

/-- Sections of an injective module sheaf restrict surjectively along an
inclusion of open subsets. -/
@[stacks 01EA "restriction of sections of an injective module sheaf"]
theorem restriction_surjective_of_injective
    {I : X.Modules} (hI : Injective I) (hVU : V ≤ U) :
    Function.Surjective
      (((SheafOfModules.forget X.ringCatSheaf).obj I).map (homOfLE hVU).op) := sorry

/-- The underlying additive restriction maps of an injective module sheaf are surjective. -/
@[stacks 01EA "underlying additive restriction of an injective module sheaf"]
theorem underlying_restriction_surjective_of_injective
    {I : X.Modules} (hI : Injective I) (hVU : V ≤ U) :
    Function.Surjective (((moduleUnderlyingSheaf X).obj I).presheaf.map (homOfLE hVU).op) := sorry

end AlgebraicGeometry.RingedSpace.Modules

end
