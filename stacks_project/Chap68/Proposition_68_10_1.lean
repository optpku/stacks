module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.Reasonable
import StacksCheckRecall

/-!
# Dense schematic locus of reasonable algebraic spaces

If an algebraic space is reasonable, then it has a dense open subspace which is
a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Proposition 68.10.1: Let `S` be a scheme. Let `X` be an algebraic space
over `S`. If `X` is reasonable, then there exists a dense open subspace of `X`
which is a scheme. -/
@[stacks 03JI] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme_of_isReasonable :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReasonable X],
      ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet)

/- If `X` is reasonable, then the schematic locus of `X` is dense in `Points X`. -/
#check (AlgebraicGeometry.AlgebraicSpace.dense_schematicLocus_of_isReasonable :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReasonable X],
    Dense (schematicLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
