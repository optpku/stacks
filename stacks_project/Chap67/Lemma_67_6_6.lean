/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.Field
import StacksCheckRecall

/-!
# Morphisms of algebraic spaces over a field are universally open

A morphism of algebraic spaces over a scheme `S` to the spectrum of a field is
universally open.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.6.6: Let `S` be a scheme. Let `p : X ⟶ ofOver (Over.mk σ)` be a
morphism of algebraic spaces over `S`, where `σ : Spec (.of k) ⟶ S` and `k` is
a field. Then `p` is universally open. -/
@[stacks 06DN] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.of_over_field :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S} (p : X ⟶ ofOver (Over.mk σ)), UniversallyOpen p)

end AlgebraicGeometry.AlgebraicSpace
