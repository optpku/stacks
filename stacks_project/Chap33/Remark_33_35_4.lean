module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Remark 33.35.4: over an infinite field, a finite family of coherent modules on a
positive-dimensional projective space admits one common nonzero hyperplane section for which
all the canonical hyperplane-section sequences are short exact. -/
@[stacks 08A1] #check
  (AlgebraicGeometry.exists_nonzero_hyperplaneSection_shortExact_of_coherent_finiteFamily :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) [Infinite k],
      1 ≤ n →
        ∀ (m : ℕ) (F : Fin m → P.scheme.Modules),
          (∀ j, (F j).IsCoherent) →
            ∃ s : P.tautologicalSheaf.sections,
              P.tautologicalSheaf.unitHomEquiv.symm s ≠
                  (0 : (SheafOfModules.unit P.scheme.ringCatSheaf : P.scheme.Modules) ⟶
                    P.tautologicalSheaf) ∧
                ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s) ∧
                  ∀ j, AlgebraicGeometry.hyperplaneSectionShortExactFor P (F j) s)
