/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections.FieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.39.5: base change along a field extension of a separably closed field
preserves global sections of every sheaf on the small étale site. -/
@[stacks 0A3I] #check
  (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection_bijective_baseChange_of_isSepClosed :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k]
      {S : Scheme.{u}} (σ : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Function.Bijective (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection
        (AlgebraicGeometry.FieldExtension.toSource k K σ) F))
