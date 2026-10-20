/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.Field
public import stacks_project.Chap66.Definition_66_4_1_Points

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.10.8: if `S` is a scheme, `k` is a field, and
`f : X ⟶ ofOver (Over.mk σ)` is a monomorphism of algebraic spaces over `S`
toward `Spec (CommRingCat.of k)`, then either `IsEmpty (Points X)` or `IsIso f`,
so `X` is empty or equal to `Spec (CommRingCat.of k)`. -/
@[stacks 06MG] #check
  (AlgebraicGeometry.AlgebraicSpace.isEmpty_or_isIso_of_mono_over_field :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] {X : AlgebraicSpace S}
      (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ)) [Mono f],
      IsEmpty (Points X) ∨ IsIso f)

/- A monomorphism of algebraic spaces over a scheme `S` toward
`Spec (CommRingCat.of k)` is an isomorphism if and only if `X` is nonempty. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_iff_nonempty_of_mono_over_field :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k] {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ)) [Mono f],
    IsIso f ↔ Nonempty (Points X))

end AlgebraicGeometry.AlgebraicSpace
