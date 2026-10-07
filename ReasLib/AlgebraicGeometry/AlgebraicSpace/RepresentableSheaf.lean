module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A presheaf on the fppf site over a scheme is a sheaf if it maps by a
representable-by-algebraic-spaces morphism to a sheaf. -/
theorem isSheaf_fppfTopology_over_of_relativelyRepresentableByAlgebraicSpaces
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : AlgebraicSpace.representableByAlgebraicSpaces a)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

end AlgebraicGeometry
