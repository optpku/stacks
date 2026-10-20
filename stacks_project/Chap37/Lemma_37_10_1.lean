/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 37.10.1: for a morphism of first-order thickenings whose map on the closed
subschemes is flat, flatness of the ambient map together with cartesianness is equivalent
to the canonical conormal comparison being an isomorphism. -/
@[stacks 063Y] #check
  (AlgebraicGeometry.IsFirstOrderThickening.flat_ambient_and_isPullback_iff_conormalMap_isIso :
    ∀ {X X' S S' : AlgebraicGeometry.Scheme.{u}} {iX : X ⟶ X'} {iS : S ⟶ S'}
      [AlgebraicGeometry.IsFirstOrderThickening iX]
      [AlgebraicGeometry.IsFirstOrderThickening iS]
      {f : X ⟶ S} {f' : X' ⟶ S'} [AlgebraicGeometry.Flat f]
      (sq : CommSq f iX iS f'),
      (AlgebraicGeometry.Flat f' ∧ IsPullback f iX iS f') ↔
        IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.map sq))
