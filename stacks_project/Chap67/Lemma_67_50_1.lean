/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.SchemeImage
import StacksCheckRecall

/-!
# Neighbourhood schemes for separated locally quasi-finite morphisms

The image of a quasi-affine open in an étale base change of a separated,
locally quasi-finite morphism of algebraic spaces is a quasi-compact open
subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.50.1. The image of the given quasi-affine open subspace is a
quasi-compact open subspace representable by a scheme. -/
@[stacks 03XW] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_quasiCompact_scheme_image :
    ∀ {S : Scheme.{u}}
      {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
      {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
      [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
      [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')],
      ∃ U : OpenSubspace X,
        U.pointsSet = Set.range (Points.map (V'.ι ≫ pX)) ∧
          IsQuasiCompact U.X ∧ IsScheme U.X)

end AlgebraicGeometry.AlgebraicSpace
