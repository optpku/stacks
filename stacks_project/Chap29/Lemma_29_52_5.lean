module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.52.5: For a locally finite-type morphism `f : X ⟶ Y` with `Y` locally
Noetherian, `topologicalKrullDim X` is at most `topologicalKrullDim Y` plus the supremum
of the residue-field transcendence degrees at the generic points of the irreducible
components of `X`. -/
@[stacks 0BAG] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.topologicalKrullDim_le_add_genericComponentTrdeg :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y],
      topologicalKrullDim X ≤ topologicalKrullDim Y +
        (((⨆ Z : irreducibleComponents X,
          (f.residueFieldTrdegAt (genericPoints.ofComponent Z) : ℕ∞)) : ℕ∞) : WithBot ℕ∞))
