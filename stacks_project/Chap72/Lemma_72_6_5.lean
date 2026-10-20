module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.SchematicLocus
import StacksCheckRecall

/-!
# Agreement of orders of vanishing on the schematic locus

On a locally Noetherian integral algebraic space, the order of a rational unit
along a prime divisor meeting the schematic locus agrees with the scheme order
on an open scheme neighborhood of its generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.6.5. The order along a prime divisor meeting the schematic locus
agrees with the scheme order of the canonically restricted rational unit. -/
@[stacks 0ENM] #check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.ord_eq_primeDivisorOrder :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ),
    (Z.pointsSet ∩ (schematicLocus X).pointsSet).Nonempty →
    ∀ {U : Over S} (ι : ofOver U ⟶ X) [IsOpenImmersion ι]
      [AlgebraicGeometry.IsLocallyNoetherian U.left] [AlgebraicGeometry.IsIntegral U.left]
      (Z' : AlgebraicGeometry.PrimeDivisor U.left),
      Points.mapOfOver ι Z'.genericPoint = Z.genericPoint →
      Z.ord f = Scheme.primeDivisorOrder U.left Z' (rationalUnitToSchemeFunctionField ι f))

#check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.exists_openImmersion_of_mem_schematicLocus :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X),
    Z.genericPoint ∈ (schematicLocus X).pointsSet →
    ∃ (U : Over S) (ι : ofOver U ⟶ X) (Z' : AlgebraicGeometry.PrimeDivisor U.left),
      IsOpenImmersion ι ∧ AlgebraicGeometry.IsLocallyNoetherian U.left ∧
        AlgebraicGeometry.IsIntegral U.left ∧
          Points.mapOfOver ι Z'.genericPoint = Z.genericPoint)

#check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.meetsSchematicLocus_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X] (Z : PrimeDivisor X),
    (Z.pointsSet ∩ (schematicLocus X).pointsSet).Nonempty ↔
      Z.genericPoint ∈ (schematicLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
