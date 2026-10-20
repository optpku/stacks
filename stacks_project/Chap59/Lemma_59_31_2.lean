/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionSupport
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

/- Lemma 59.31.2 (1): an abelian étale-sheaf section has a largest Zariski open
on which its restriction vanishes. -/
@[stacks 04FR] #check
  (AlgebraicGeometry.Scheme.Etale.exists_largest_vanishing_open :
    ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (U : S.Etale) (σ : F.1.obj (Opposite.op U)),
      ∃ W : U.left.Opens,
        AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ W ∧
          ∀ V : U.left.Opens,
            AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ V → V ≤ W)

/- Lemma 59.31.2 (2): vanishing after an étale map is equivalent to its image
lying in the largest vanishing open. -/
@[stacks 04FR] #check
  (AlgebraicGeometry.Scheme.Etale.restrict_eq_zero_iff_image_subset :
    ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (U : S.Etale) (σ : F.1.obj (Opposite.op U)) (W : U.left.Opens)
      (hW : AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ W)
      (hmax : ∀ V : U.left.Opens,
        AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ V → V ≤ W)
      {V : S.Etale} (φ : V ⟶ U),
      F.1.map φ.op σ = 0 ↔ Set.range φ.left ⊆ (W : Set U.left))

/- Lemma 59.31.2 (3): the geometric germ vanishes exactly at geometric points
lying in the largest vanishing open. -/
@[stacks 04FR] #check
  (AlgebraicGeometry.Scheme.Etale.geometric_germ_eq_zero_iff_mem :
    ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (U : S.Etale) (σ : F.1.obj (Opposite.op U)) (W : U.left.Opens)
      (hW : AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ W)
      (hmax : ∀ V : U.left.Opens,
        AlgebraicGeometry.Scheme.Etale.vanishesOn F U σ V → V ≤ W)
      (ū : Scheme.GeometricPoint U.left),
      AlgebraicGeometry.Scheme.Etale.geometricGerm U F σ ū = 0 ↔ ū.image ∈ W)
