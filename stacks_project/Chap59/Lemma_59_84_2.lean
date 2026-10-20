/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Finiteness

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory GrothendieckTopology

noncomputable section

universe u v w

/- Lemma 59.84.2: for a Noetherian ring `Λ`, an algebraically closed field `k`,
and a finite morphism `f : X.left ⟶ Y.left` of separated finite-type `k`-schemes
of dimension at most one, if the canonical module-valued degree-`q` étale
cohomology of `F` is a finite `Λ`-module, then the same holds for `Y` and the
continuous sheaf pushforward of `smallEtalePullback f`. -/
@[stacks 0GJD] #check (AlgebraicGeometry.Scheme.Etale.finiteCohomologyOfFinitePushforward :
    ∀
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X Y : SchemeOverField k)
    [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    (f : X.left ⟶ Y.left) [IsFinite f] (h_over : f ≫ Y.hom = X.hom)
    (hX : topologicalKrullDim X.left ≤ 1)
    (hY : topologicalKrullDim Y.left ≤ 1)
    (q : ℕ) (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasWeakSheafify Y.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasExt (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    [Y.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    [Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := X.left.smallEtaleTopology) (A := Λ) q).obj F)],
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor
        (J := Y.left.smallEtaleTopology) (A := Λ) q).obj
          (((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{max u (v + 1)} Λ)
              Y.left.smallEtaleTopology X.left.smallEtaleTopology).obj F)))
