/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskisMainTheorem
import StacksCheckRecall

/-!
# Zariski's Main Theorem, representable case

A representable finite-type separated morphism of algebraic spaces is an
isomorphism over an open subspace of its relative normalization, whose inverse
image is exactly the quasi-finite locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/- Lemma 67.52.1: Let `S` be a scheme, and let `f : X ⟶ Y` be a representable,
finite-type, separated morphism of algebraic spaces over `S`. Let `Y'` be the
normalization of `Y` in `X`, with the canonical factorization
`X ⟶ normalization f ⟶ Y` given by `toNormalization f` and
`fromNormalization f`. Then there exists an open subspace
`ι : U' ⟶ normalization f` such that
`openInverseImageTo (toNormalization f) ι` is an isomorphism, and the points of
`openInverseImageι (toNormalization f) ι` in `X` are exactly the points at which
`f` is quasi-finite. -/
@[stacks 0ABR] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.exists_isIso_openInverseImageTo_toNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [FiniteType f] [Separated f],
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          setOf (QuasiFiniteAt f))

end Hom

end AlgebraicGeometry.AlgebraicSpace
