/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.HigherDirectImage.Colimits

/-!
# Lemma 69.5.2

Filtered colimits of abelian étale sheaves commute with higher direct images along a
quasi-compact quasi-separated morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u v

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.5.2. Higher direct images along quasi-compact quasi-separated morphisms
of algebraic spaces commute with filtered colimits of abelian étale sheaves. -/
@[stacks 07U6] #check
  (AlgebraicGeometry.AlgebraicSpace.higherDirectImageFunctor_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
      [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
      [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
      [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
      [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
      [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
      {I : Type v} [SmallCategory I] [IsFiltered I]
      (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      [HasColimit ℱ] (p : ℕ)
      [HasColimit (ℱ ⋙ higherDirectImageFunctor f p)],
      IsIso (colimit.post ℱ (higherDirectImageFunctor f p)))
