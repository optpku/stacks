module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- If degree-`d` cohomology of a coherent module on a variety is nonzero, then
`d` is at most the dimension of the variety. -/
theorem cohomologyDegree_le_dimension {k : Type u} [Field k]
    (U : SchemeOverField k) [Variety U]
    (F : U.left.Modules) [F.IsCoherent] (d : ℕ)
    (h_nonzero : ¬ IsZero (Scheme.Modules.cohomology F d)) :
    d ≤ U.dimension := sorry

/-- If degree-`d` cohomology of a coherent module on a dimension-`d` variety is
nonzero, then the structure morphism of the variety is proper. -/
theorem isProper_of_dimension_eq_cohomologyDegree {k : Type u} [Field k]
    (U : SchemeOverField k) [Variety U]
    (F : U.left.Modules) [F.IsCoherent] (d : ℕ)
    (h_nonzero : ¬ IsZero (Scheme.Modules.cohomology F d)) :
    U.dimension = d → IsProper U.hom := sorry

end AlgebraicGeometry.SchemeOverField

end
