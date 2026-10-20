module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower-truncation resolution limits on ringed spaces

This leaf joins the generic injective lower-truncation resolution API to the local
cohomological convergence criteria for modules on a ringed space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation.Resolution

variable {X : RingedSpace.{u}}

/-- Uniform negative cohomology vanishing on an open basis makes the canonical map into the
limit of an injective lower-truncation resolution a quasi-isomorphism. -/
@[stacks 071B "lower-truncation resolution limit is a quasi-isomorphism"]
theorem intoLimit_quasiIso
    (F : CochainComplex X.Modules ℤ)
    (S : CochainComplex.LowerTruncation.Resolution (isInjective X.Modules) F)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑) (d : ℕ)
    (hF : Basis.Negative (DerivedCategory.Q.obj F) d 𝓑) :
    QuasiIso S.intoLimit := sorry

/-- Source-facing companion of `intoLimit_quasiIso`, phrased using ordinary cohomology of the
underlying additive cohomology sheaves. -/
@[stacks 071B "lower-truncation resolution limit from underlying-sheaf vanishing"]
theorem intoLimit_quasiIso_ofSheaves
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (F : CochainComplex X.Modules ℤ)
    (S : CochainComplex.LowerTruncation.Resolution (isInjective X.Modules) F)
    {𝓑 : Set (Opens X.carrier)} (h𝓑 : Opens.IsBasis 𝓑) (d : ℕ)
    (hF : Basis.SheafNegative (DerivedCategory.Q.obj F) d 𝓑) :
    QuasiIso S.intoLimit := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation.Resolution

end
