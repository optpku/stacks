/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_82_2
public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.GabberH0
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.82.6: if `(A, I)` is a henselian pair, `X = Spec A` and
`Z = Spec (A ⧸ I)`, then for any sheaf `F` on `X_étale` the canonical restriction
`etaleGlobalSectionsPullback` identifies `Γ(X, F)` with `Γ(Z, F|_Z)`. -/
@[stacks 09ZH] #check (AlgebraicGeometry.Scheme.etaleGlobalSections_bijective_of_henselianPair : ∀
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    [HasWeakSheafify (Spec (CommRingCat.of A)).smallEtaleTopology (Type u)]
    [HasWeakSheafify (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology (Type u)]
    [∀ P : (Spec (CommRingCat.of A)).Etaleᵒᵖ ⥤ Type u,
      (smallEtalePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).op.HasLeftKanExtension P]
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (Type u)),
    Function.Bijective
      (etaleGlobalSectionsPullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F))

end AlgebraicGeometry.Scheme

end
