/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.GenericPoints
import StacksCheckRecall

/-!
# Codimension-zero points of algebraic spaces

A point of an algebraic space has codimension `0` if and only if some, equivalently every,
étale scheme chart through that point is a generic point of an irreducible component of the
source scheme. When the algebraic space is representable this is the usual generic-point
condition on the underlying space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.11.1 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `X`. Then `x` is a point of codimension `0` on `X` if and only if some étale
scheme chart through `x` is a generic point of an irreducible component of the source scheme. -/
@[stacks 0BAQ] #check
  (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_zero_iff_existsEtaleAt_mem_genericPoints :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
      localRingDimAt x = 0 ↔ existsEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x)

/- Lemma 66.11.1 (2): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `X`. Then `x` is a point of codimension `0` on `X` if and only if every étale
scheme chart through `x` is a generic point of an irreducible component of the source scheme. -/
@[stacks 0BAQ] #check
  (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_zero_iff_forallEtaleAt_mem_genericPoints :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
      localRingDimAt x = 0 ↔ forallEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x)

/- Lemma 66.11.1 (3): if `X` is representable by a scheme `T` over `S`, then the image of `t`
is a point of codimension `0` on `ofOver T` if and only if `t` is a generic point of an
irreducible component of `T.left`. This is the representable `|X|` condition via
`ofOver.pointsEquiv` and the scheme topology on `T.left`, not membership in `genericPoints` of
an unspecified topology on `Points`. -/
@[stacks 0BAQ] #check
  (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_zero_iff_mem_genericPoints_ofOver :
    ∀ {S : Scheme.{u}} (T : Over S) (t : T.left),
      localRingDimAt (ofOver.pointsEquiv T t) = 0 ↔ t ∈ _root_.genericPoints T.left)

end AlgebraicGeometry.AlgebraicSpace
