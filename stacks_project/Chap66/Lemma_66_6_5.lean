/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Atlas

/-!
# Quasi-separated algebraic spaces from a quasi-separated étale atlas

A surjective étale atlas from a quasi-separated scheme with either kernel-pair
projection quasi-compact makes the algebraic space absolutely quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.6.5: A surjective étale atlas from a quasi-separated scheme
with either kernel-pair projection quasi-compact makes the algebraic space
absolutely quasi-separated. -/
@[stacks 07S4] #check
  (AlgebraicGeometry.AlgebraicSpace.isAbsolutelyQuasiSeparated_of_etale_atlas :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
      [QuasiSeparatedSpace U.left] (φ : ofOver U ⟶ X)
      (h_etale : (MorphismProperty.over (@Etale)).presheaf φ)
      (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
      (h_qc : QuasiCompact (kernelPair φ h_etale.rep).t.left ∨
        QuasiCompact (kernelPair φ h_etale.rep).s.left),
      IsAbsolutelyQuasiSeparated X)

end AlgebraicGeometry.AlgebraicSpace
