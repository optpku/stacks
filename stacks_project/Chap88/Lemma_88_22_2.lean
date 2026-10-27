/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FlatLocus.RigDiagonal

/-!
# Lemma 88.22.2

A locally Noetherian formal algebraic space locally of finite type over a
complete discrete valuation ring, whose relative diagonal is both rig-étale
and rig-surjective, has flat locus isomorphic to the formal spectrum or empty.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

universe u

/- Lemma 88.22.2: let `X` be a locally Noetherian formal algebraic space which
is locally of finite type over a complete discrete valuation ring `A`. Let
`X' ⊂ X` be the flat locus of Lemma 88.22.1, realized as `flatLocus p` with
closed immersion `flatLocusι p`. If the relative diagonal
`pullback.diagonal p : X ⟶ pullback p p` is rig-étale and rig-surjective, then
`flatLocusι p ≫ p` is an isomorphism, or else every test scheme admitting
a section of `flatLocus p` is empty. -/
@[stacks 0GD9] #check (AlgebraicGeometry.FormalAlgebraicSpace.flatLocus_eq_spf_or_empty :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA)
    [LocallyOfFiniteType p] [RigEtale (pullback.diagonal p)]
    [RigSurjective (pullback.diagonal p)],
    IsIso (flatLocusι p ≫ p) ∨
      ∀ T : Over S, (flatLocus p).obj (Opposite.op T) → IsEmpty T.left)
