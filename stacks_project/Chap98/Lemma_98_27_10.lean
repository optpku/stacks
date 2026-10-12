/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_27_4_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Étale sheafness of the Artin contraction functor

In Situation 98.27.1 the contraction functor on locally Noetherian schemes
over `S` is a sheaf for the étale topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.10: In Situation 98.27.1 the functor `σ.functor` satisfies the
sheaf property for all étale coverings of locally Noetherian schemes over `S`. -/
@[stacks 0GHG]
theorem isSheaf_etale (σ : ContractionSituation S) :
    Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S)
      σ.functor :=
  sorry

/-- The covering-sieve form of étale sheafness of `σ.functor` on locally
Noetherian schemes over `S`. -/
theorem isSheafFor_etaleCover (σ : ContractionSituation S)
    {V : (locallyNoetherian S).FullSubcategory} (R : Sieve V)
    (hR : R ∈ locallyNoetherianTopology StandardTopology.etale S V) :
    Presieve.IsSheafFor σ.functor R.arrows :=
  sorry

/-- Étale sheafness of `σ.functor` is equivalent to the type-valued sheaf
condition `Presieve.IsSheaf` on the locally Noetherian étale site. -/
theorem isSheaf_etale_iff (σ : ContractionSituation S) :
    Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S)
        σ.functor ↔
      Presieve.IsSheaf (locallyNoetherianTopology StandardTopology.etale S)
        σ.functor :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
