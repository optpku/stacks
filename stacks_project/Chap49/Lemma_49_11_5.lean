/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.EtaleLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace UniversalFiniteFreeAlgebra

/- Lemma 49.11.5: the maximal target open on which the universal finite free family
is étale is dense in an open classifying exactly its syntomic base changes. -/
@[stacks 0FL2] #check (UniversalFiniteFreeAlgebra.etaleTargetLocus_denseRange :
  ∀ (d : ℕ+) (U_d : (baseScheme d).Opens),
    (hU_d : ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) →
      DenseRange ((baseScheme d).homOfLE
        (etaleTargetLocus_le d U_d hU_d)))

end UniversalFiniteFreeAlgebra
