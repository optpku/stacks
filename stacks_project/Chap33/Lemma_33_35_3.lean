module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

/- Lemma 33.35.3: over an infinite field, a coherent module on positive-dimensional
projective space admits a nonzero tautological section whose hyperplane-section complex is
short exact. -/
@[stacks 08A0]
#check
  (AlgebraicGeometry.exists_nonzero_hyperplaneSection_shortExact_of_coherent :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
      [Infinite k] (hn : 1 ≤ n) (F : P.scheme.Modules) [F.IsCoherent],
      ∃ s : P.tautologicalSheaf.sections,
        P.tautologicalSheaf.unitHomEquiv.symm s ≠
            (0 : (SheafOfModules.unit P.scheme.ringCatSheaf : P.scheme.Modules) ⟶
              P.tautologicalSheaf) ∧
          ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s) ∧
            (hyperplaneSectionSequence P F s).ShortExact)
