/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DenseOpen.Separated
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 110.27.2: there exists a quasi-compact and quasi-separated scheme `X`
which does not contain a separated quasi-compact dense open. -/
@[stacks 086I]
#check (AlgebraicGeometry.Scheme.exists_qcqs_no_separated_quasiCompact_dense_open :
    ∃ (X : Scheme.{u}),
      CompactSpace X ∧
        QuasiSeparatedSpace X ∧
          ¬ ∃ (U : X.Opens),
              Dense (U : Set X) ∧ IsCompact (U : Set X) ∧ U.toScheme.IsSeparated)
