/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus

/-!
# Zariski's Main Theorem, finite-type separated case

A finite-type separated morphism of algebraic spaces is an isomorphism over an
open subspace of its relative normalization, whose inverse image is exactly the
quasi-finite locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.34.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is of finite type and separated. Let `Y'` be
the normalization of `Y` in `X`, namely `Hom.normalization f`, with the
canonical factorization `toNormalization f ≫ fromNormalization f = f`. Then
there exists an open subspace `ι : U' ⟶ Hom.normalization f` such that
`openInverseImageTo (toNormalization f) ι` is an isomorphism, and
`Set.range (Points.map (openInverseImageι (toNormalization f) ι))` is the set
of points of `X` at which `f` is quasi-finite. -/
@[stacks 082I]
theorem FiniteType.exists_isIso_openInverseImageTo_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f] :
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          {x | QuasiFiniteAt f x} :=
  sorry

/-- The open inverse image of the finite-type separated Zariski main theorem
open is the image of `quasiFiniteLocus f` in `|X|`. -/
theorem FiniteType.exists_isIso_openInverseImageTo_toNormalization_quasiFiniteLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f] :
    ∃ (U' : AlgebraicSpace S) (ι : U' ⟶ normalization f)
      (hι : IsOpenImmersion ι),
      IsIso (openInverseImageTo (toNormalization f) ι) ∧
        Set.range (Points.map (openInverseImageι (toNormalization f) ι)) =
          Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
