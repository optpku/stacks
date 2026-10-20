/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import stacks_project.Chap76.Lemma_76_44_1_EtaleLocalOnTarget

/-!
# Étale-local-on-the-target properties of representable morphisms

A scheme-morphism property that is étale local on the target may be tested on
every étale scheme pullback of a representable morphism of algebraic spaces, or
equivalently on some surjective étale scheme pullback. On representable spaces
this recovers the underlying scheme morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.44.1 (1): a representable morphism of algebraic spaces over `S` has
the étale-on-target lift of `P` if and only if some commutative diagram with
étale `V ⟶ Y` from a scheme and étale-locally surjective atlas has projection
`X ×_Y V ⟶ V` satisfying `P`. -/
@[stacks 06BM] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget_iff_existsSurjectivePullback :
  ∀ {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f),

    etaleLocalOnTarget P f ↔ etaleLocalOnTarget.existsSurjectivePullback P f)

/- Lemma 76.44.1 (2): if `X` and `Y` are representable, then the étale-on-target
lift of `P` on the induced morphism of algebraic spaces is equivalent to the
underlying scheme morphism having `P`. -/
@[stacks 06BM] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget_ofOverMap_iff :
  ∀ {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {U V : Over S} (h : U ⟶ V),

    etaleLocalOnTarget P (ofOverMap h) ↔ P h.left)

end AlgebraicGeometry.AlgebraicSpace
