module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Cohomology.InverseSystem
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- If `I` has local-cohomological dimension one, then in every integer degree the
limit topology on the cohomology system of a coherent formal module over a Noetherian
scheme is the `I`-adic module topology. -/
theorem cohomologyLimitTopology_eq_adic
    (I : Ideal A) {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.CoherentFormalModules
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f))
    (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
    (p : ℤ) :
    Functor.limitTopology (cohomologySystem F f p) =
      Ideal.adicModuleTopology I
        (limit (cohomologySystem F f p) : ModuleCat A) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
