/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.SeparablyClosed
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

universe u

/- Lemma 59.83.12: canonical étale cohomology pullback for a locally torsion abelian
sheaf on a proper scheme of dimension at most one is an isomorphism in every degree
under an extension of separably closed fields. -/
@[stacks 0A5E] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.cohomologyPullback_isIso_of_isProper_of_isSepClosed :
    ∀ [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      {k : Type u} [Field k] [IsSepClosed k]
      (X : SchemeOverField k) (h_dim : topologicalKrullDim X.left ≤ 1)
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
      (hF : IsLocallyTorsion F) (h_proper : IsProper X.hom)
      {k' : Type u} [Field k'] [IsSepClosed k'] [Algebra k k']
      (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
      (h_baseChange : IsPullback π X'.hom X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (q : ℕ), IsIso (cohomologyPullback π F q))
