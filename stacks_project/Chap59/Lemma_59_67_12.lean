/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.FunctionField
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale.Small

universe u

/- Lemma 59.67.12: if `k` is algebraically closed and `K / k` has transcendence degree
one, then small étale cohomology of `Spec K` with coefficients in the multiplicative-group
sheaf vanishes in every degree `q ≥ 1`. -/
@[stacks 03RG] #check
  (AlgebraicGeometry.Scheme.Etale.Small.etaleUnitsCohomology_isZero_of_trdeg_one :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K]
    (htr : Algebra.trdeg k K = 1)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 1 ≤ q),
    IsZero ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology q).obj
      (unitsAddSheaf (Spec (.of K)))))
