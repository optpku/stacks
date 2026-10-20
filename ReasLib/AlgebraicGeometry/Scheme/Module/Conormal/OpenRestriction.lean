module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion

/-!
# Conormal sheaves under restriction to an open subscheme

A closed immersion into an open subscheme has the same conormal sheaf as its
composite with the open immersion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {Z U X : Scheme.{u}}

/-- Restricting the ambient scheme of a closed immersion to an open subscheme gives an
explicit equivalence of conormal sheaves. -/
noncomputable def openRestrictionEquiv
    (i : Z ⟶ X) (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k] :
    Scheme.Hom.conormalSheaf i ≅ Scheme.Hom.conormalSheaf j :=
  factorizationConormalComparisonIso i j k h

end AlgebraicGeometry.Scheme.Hom.Conormal

