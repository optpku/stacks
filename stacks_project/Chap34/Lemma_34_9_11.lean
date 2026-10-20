/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Stability
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 34.9.11 (1): an isomorphism onto an affine scheme gives a singleton
standard fpqc cover. -/
@[stacks 03LA] #check
  (AlgebraicGeometry.StandardFpqcCover.singletonOfIsIso :
    {T T' : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsAffine T] →
      (f : T' ⟶ T) → [IsIso f] → AlgebraicGeometry.StandardFpqcCover T)

#check
  (AlgebraicGeometry.StandardFpqcCover.singletonOfIsIso_toOverFamily_obj :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
      (f : T' ⟶ T) [IsIso f] (j : Fin 1),
      (AlgebraicGeometry.StandardFpqcCover.singletonOfIsIso f).toOverFamily.obj j =
        Over.mk f)

/- Lemma 34.9.11 (2): dependent composition preserves standard fpqc covers. -/
@[stacks 03LA] #check
  (AlgebraicGeometry.StandardFpqcCover.comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}
      (cover : AlgebraicGeometry.StandardFpqcCover T)
      (refinement : ∀ i : Fin cover.n,
        AlgebraicGeometry.StandardFpqcCover (cover.U i)),
      AlgebraicGeometry.StandardFpqcCover T)

#check
  (AlgebraicGeometry.StandardFpqcCover.comp_toOverFamily_obj :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}
      (cover : AlgebraicGeometry.StandardFpqcCover T)
      (refinement : ∀ i : Fin cover.n,
        AlgebraicGeometry.StandardFpqcCover (cover.U i))
      (ij : Sigma fun i : Fin cover.n ↦ Fin (refinement i).n),
      (AlgebraicGeometry.StandardFpqcCover.comp cover refinement).toOverFamily.obj
          (finSigmaFinEquiv ij) =
        Over.mk ((refinement ij.1).map ij.2 ≫ cover.map ij.1))

/- Lemma 34.9.11 (3): base change to an affine scheme preserves standard fpqc
covers. -/
@[stacks 03LA] #check
  (AlgebraicGeometry.StandardFpqcCover.pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T']
      (cover : AlgebraicGeometry.StandardFpqcCover T) (f : T' ⟶ T),
      AlgebraicGeometry.StandardFpqcCover T')

#check
  (AlgebraicGeometry.StandardFpqcCover.pullback_toOverFamily_obj :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T']
      (cover : AlgebraicGeometry.StandardFpqcCover T) (f : T' ⟶ T)
      (i : Fin cover.n),
      (AlgebraicGeometry.StandardFpqcCover.pullback cover f).toOverFamily.obj i =
        Over.mk (Limits.pullback.fst f (cover.map i)))
