/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Translation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 40.10.6 (1): left translation at a residue-field point is an isomorphism. -/
@[stacks 04LS] #check
  (AlgebraicGeometry.GroupoidScheme.isIso_leftTranslationAt :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
      [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)]
      [IsIso (G.R.left.fromSpecResidueField r ≫ G.t.left ≫ uIso.hom)],
      IsIso (G.leftTranslationAt uIso r))

/- Lemma 40.10.6 (2): translation sends the distinguished identity point to r. -/
@[stacks 04LS] #check
  (AlgebraicGeometry.GroupoidScheme.leftTranslationAt_mapsIdentity :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
      [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)]
      [IsIso (G.R.left.fromSpecResidueField r ≫ G.t.left ≫ uIso.hom)],
      (G.leftTranslationAt uIso r).left
          (G.e.left (uIso.inv (IsLocalRing.closedPoint K))) = r)

end AlgebraicGeometry.GroupoidScheme
