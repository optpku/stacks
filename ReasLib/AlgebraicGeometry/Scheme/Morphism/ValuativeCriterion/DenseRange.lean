module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Factorization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ValuativeCriterion.Along

/-- A restricted valuative existence-and-uniqueness criterion along a quasi-compact morphism
with dense range implies universal closedness. -/
theorem universallyClosed {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [QuasiCompact f] [QuasiCompact h] (h_dense : DenseRange h)
    (h_criterion : ExistsUnique h f) : UniversallyClosed f := sorry

/-- A quasi-separated morphism satisfying a restricted valuative existence-and-uniqueness
criterion along a quasi-compact morphism with dense range is separated. -/
theorem isSeparated {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [QuasiCompact f] [QuasiCompact h] [QuasiSeparated f] (h_dense : DenseRange h)
    (h_criterion : ExistsUnique h f) : IsSeparated f := sorry

end AlgebraicGeometry.ValuativeCriterion.Along
