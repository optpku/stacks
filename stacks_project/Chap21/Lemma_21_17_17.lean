module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Factorization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.17

K-flat homotopy factorization is owned by the ringed-site ReasLib leaf.  The chapter keeps the
homotopy, termwise-flat, and degreewise-flat formulations as separate recalls, with no local
monoidal or additive instance reconstruction.
-/

open SheafOfModules.RingedSite

/- Lemma 21.17.17 (0G7D) (1): factorization through a K-flat quasi-isomorphism up to homotopy. -/
@[stacks 0G7D "K-flat homotopy factorization"] #check
  @exists_homotopy_factorization_through_kFlat_quasiIso

/- Lemma 21.17.17 (0G7D) (2): termwise-flat source data can be preserved by the factorization. -/
@[stacks 0G7D "termwise-flat K-flat homotopy factorization"] #check
  @exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso

/- Lemma 21.17.17 (0G7D) (3): degreewise flatness is the source-facing specialization. -/
@[stacks 0G7D "degreewise-flat K-flat homotopy factorization"] #check
  @exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
