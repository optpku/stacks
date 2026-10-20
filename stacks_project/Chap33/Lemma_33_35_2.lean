/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hyperplane
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 33.35.2: if `k` is a field, `1 ≤ n`, and `i : H ⟶ ℙ^n_k` is a hyperplane, then there
exists a projective-space model `ℙ^(n - 1)_k` together with an isomorphism `φ : ℙ^(n - 1)_k ≅ H`
over `Spec (CommRingCat.of k)` such that the pullback of `i^*𝒪(1)` along `φ` is isomorphic to
`𝒪(1)` on `ℙ^(n - 1)_k`. -/
@[stacks 089Z] #check
  (AlgebraicGeometry.exists_iso_projectiveSpace_pred_pullback_tautologicalSheaf_of_hyperplane :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) (hn : 1 ≤ n)
      {H : Scheme.{u}} (i : H ⟶ P.scheme)
      (hHyperplane : ProjectiveSpaceHyperplane P i),
      ∃ (P' : ProjectiveSpaceOver (Spec (CommRingCat.of k)) (n - 1)) (φ : P'.scheme ≅ H)
        (e :
          (Scheme.Modules.pullback φ.hom).obj
              ((Scheme.Modules.pullback i).obj P.tautologicalSheaf) ≅
            P'.tautologicalSheaf),
        φ.hom ≫ i ≫ P.hom = P'.hom)
