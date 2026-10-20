module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-`i` cohomology sheaf of a derived `𝒪_X`-module. -/
abbrev cohomologySheaf (E : ModuleDerived X) (i : ℤ) : X.Modules :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj E

/-- The degree-`i` cohomology sheaf is the homology functor applied to `E`. -/
theorem cohomologySheaf_eq (E : ModuleDerived X) (i : ℤ) :
    cohomologySheaf E i = (DerivedCategory.homologyFunctor (Modules X) i).obj E :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
