/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

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

/-- Lemma 67.52.1: Let `S` be a scheme, and let `f : X ⟶ Y` be a representable,
finite-type, separated morphism of algebraic spaces over `S`. Let `Y'` be the
normalization of `Y` in `X`, with the canonical factorization
`X ⟶ normalization f ⟶ Y` given by `toNormalization f` and
`fromNormalization f`. Then there exists an open subspace
`ι : U' ⟶ normalization f` such that
`openInverseImageTo (toNormalization f) ι` is an isomorphism, and the points of
`openInverseImageι (toNormalization f) ι` in `X` are exactly the points at which
`f` is quasi-finite. -/
@[stacks 0ABR]
theorem exists_isIso_openInverseImageTo_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [FiniteType f] [Separated f] :
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          setOf (QuasiFiniteAt f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
