/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.Descent

/-!
# Étale-local properties of morphisms of algebraic spaces

A scheme-morphism property that is étale local on source-and-target may be
tested on a single surjective étale scheme square. On representable spaces this
recovers the underlying scheme morphism, and on representable morphisms it
recovers the Section 67.3 / Definition 65.5.1 predicate when `P` is stable under
base change and fppf local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.22.1 (1): a morphism of algebraic spaces over `S` has the étale-local
lift of `P` if and only if some commutative square with étale vertical arrows
from schemes and surjective source atlas has top arrow satisfying `P`. -/
@[stacks 03MJ] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_iff_existsSurjectiveSquare :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [IsEtaleLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      etaleLocal P f ↔ etaleLocal.existsSurjectiveSquare P f)

/- Lemma 67.22.1 (2): if `X` and `Y` are representable, then the étale-local lift
of `P` on the induced morphism of algebraic spaces is equivalent to the
underlying scheme morphism having `P`. -/
@[stacks 03MJ] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_ofOverMap_iff :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [IsEtaleLocalAtSourceAndTarget P] {U V : Over S} (h : U ⟶ V),
      etaleLocal P (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔ P h.left)

/- Lemma 67.22.1 (3): if `P` is stable under arbitrary base change and fppf local
on the target, then a representable morphism of algebraic spaces has the
étale-local lift of `P` if and only if it has `P` in the sense of Section 67.3. -/
@[stacks 03MJ] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_iff_over_presheaf :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget Scheme.fppfPrecoverage]
      {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      (hf : yoneda.relativelyRepresentable f),
      etaleLocal P f ↔ (over P).presheaf f)
