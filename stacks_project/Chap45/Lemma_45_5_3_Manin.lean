/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Manin
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

universe u

/- Lemma 45.5.3 (Manin): a morphism of rational Chow motives is an isomorphism if,
 after tensoring with the motive of every smooth projective scheme, it induces an
 isomorphism on every degreewise Chow group of the concrete realization. -/
@[stacks 0FGN] #check
  (ChowMotive.isIso_of_chowTensor :
    ∀ {k : Type u} [Field k]
      {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)} (c : M ⟶ N),
      (∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (i : ℤ),
          IsIso ((ChowMotive.chowFunctor (k := k) i).map
            (c ⊗ₘ 𝟙 (ChowMotive.h X)))) →
        IsIso c)
