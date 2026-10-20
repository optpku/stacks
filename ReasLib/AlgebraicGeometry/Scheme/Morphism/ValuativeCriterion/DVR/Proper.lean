module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Separated

/-!
# Properness from DVR-valuative criteria over locally Noetherian schemes

For finite-type morphisms to locally Noetherian schemes, properness can be tested using the
valuative criterion, the DVR-valuative criterion, or its restriction to canonical residue-field
maps at generic points of irreducible components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ValuativeCriterion.DVR

/-- For a finite-type morphism to a locally Noetherian scheme, properness is equivalent to the
valuative criterion, the DVR-valuative criterion, and the DVR exists-unique criterion at the
generic points of irreducible components. -/
@[stacks 0208 "Noetherian DVR-valuative criterion for properness"]
theorem isProper_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [IsLocallyNoetherian S] :
    List.TFAE
      [ IsProper f
      , ValuativeCriterion f
      , ValuativeCriterion.DVR f
      , GenericPointDvrValuativeCriterionExistsUnique f
      ] := sorry

end AlgebraicGeometry.ValuativeCriterion.DVR
