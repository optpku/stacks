/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Projective

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.15.5: let `f : X ⟶ Spec (CommRingCat.of k)` exhibit `X` as a scheme over the field
`k`, and let `K/k` be a field extension. If the base-changed structure morphism
`X ×[Spec (CommRingCat.of k)] Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)` is projective,
then `X` is projective over `k`. -/
@[stacks 0BDG] #check
  (AlgebraicGeometry.Projective.of_baseChangeToFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      Projective (FieldExtension.toBase k K f) → Projective f)
