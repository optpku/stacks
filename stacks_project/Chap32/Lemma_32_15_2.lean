module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Separated
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.15.2: for a locally finite type morphism `f : X ⟶ S` with `S` locally
Noetherian, separatedness is equivalent to valuative uniqueness, DVR-valuative uniqueness, and
DVR-valuative uniqueness for the canonical residue-field maps at generic points of irreducible
components of `X`. -/
@[stacks 0207] #check
  (AlgebraicGeometry.isSeparated_tfae_valuativeCriterion_dvr_genericPoint :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f],
      List.TFAE [
        AlgebraicGeometry.IsSeparated f,
        AlgebraicGeometry.ValuativeCriterion.Uniqueness f,
        AlgebraicGeometry.ValuativeCriterion.DVR.Uniqueness f,
        AlgebraicGeometry.GenericPointDvrValuativeCriterionUniqueness f])
