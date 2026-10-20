/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Fibers

/-!
# Comparing source fibres of a groupoid in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

section

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {K : Type u} [Field K]
variable {σK : Spec (.of K) ⟶ S}

/- Lemma 79.7.1: Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`.
Let `K` be a field and let `r`, `r' : Spec (.of K) ⟶ R` be morphisms with
`t ∘ r = t ∘ r'`. Writing `u = s ∘ r` and `u' = s ∘ r'`, the source fibres
`Spec (.of K) ×_{u, U, s} R` and `Spec (.of K) ×_{u', U, s} R` are isomorphic
as algebraic spaces over `K`. -/
@[stacks 0452] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsSourceFiberIso :
    ∀ (G : GroupoidAlgebraicSpace B)
    {r r' : AlgebraicSpace.ofOver (Over.mk σK) ⟶ G.R.left}
    (ht : r ≫ G.t.left = r' ≫ G.t.left),
    let u := r ≫ G.s.left
    let u' := r' ≫ G.s.left
    Nonempty
      (Over.mk (pullback.snd G.s.left u) ≅
        Over.mk (pullback.snd G.s.left u')))

end

end AlgebraicGeometry.GroupoidAlgebraicSpace
