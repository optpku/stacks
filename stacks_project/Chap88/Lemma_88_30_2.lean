module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap88.Lemma_88_30_1_BaseChange

/-!
# Transfer of morphism properties along 88.30.1 base change

If `A → B` induces an isomorphism of `I`-adic completions, then an
fpqc-local-on-the-target morphism property containing identities holds for a
morphism in the 88.30.0.1 category for `(A, I)` if and only if it holds for
the corresponding base change over `Spec(B)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- An fpqc-local-on-the-target morphism property of algebraic spaces that
contains identities holds for the structure morphism of `Y` over `specOver hA`
if and only if it holds for the structure morphism of the image under
`sourceBaseChangeAlgebraMap B hA I`. The image structure morphism is
`overPullbackSnd (algebraMapOver B hA) Y.obj` by
`sourceBaseChangeAlgebraMap_obj`. -/
theorem sourceBaseChangeAlgebraMap_morphismProperty_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (fpqcPrecoverage S)] [P.ContainsIdentities]
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    P Y.obj.hom ↔ P ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- Lemma 88.30.2 (1): with notation and assumptions as in Lemma 88.30.1, if
`f : X' ⟶ specOver hA` corresponds to `g : Y' ⟶ specOver (Spec.map (algebraMap A B) ≫ hA)`
via `sourceBaseChangeAlgebraMap`, then `f` is quasi-compact if and only if `g`
is. Here `f` is `Y.obj.hom` and `g` is the structure morphism of the
`sourceBaseChangeAlgebraMap` image, i.e. `overPullbackSnd (algebraMapOver B hA) Y.obj`
by `sourceBaseChangeAlgebraMap_obj`. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_quasiCompact_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    QuasiCompact Y.obj.hom ↔
      QuasiCompact ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- Lemma 88.30.2 (2): with notation and assumptions as in Lemma 88.30.1, if
`f : X' ⟶ specOver hA` corresponds to `g : Y' ⟶ specOver (Spec.map (algebraMap A B) ≫ hA)`
via `sourceBaseChangeAlgebraMap`, then `f` is quasi-separated if and only if
`g` is. Here `f` is `Y.obj.hom` and `g` is the structure morphism of the
`sourceBaseChangeAlgebraMap` image, i.e. `overPullbackSnd (algebraMapOver B hA) Y.obj`
by `sourceBaseChangeAlgebraMap_obj`. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_quasiSeparated_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    QuasiSeparated Y.obj.hom ↔
      QuasiSeparated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- Lemma 88.30.2 (3): with notation and assumptions as in Lemma 88.30.1, if
`f : X' ⟶ specOver hA` corresponds to `g : Y' ⟶ specOver (Spec.map (algebraMap A B) ≫ hA)`
via `sourceBaseChangeAlgebraMap`, then `f` is separated if and only if `g` is.
Here `f` is `Y.obj.hom` and `g` is the structure morphism of the
`sourceBaseChangeAlgebraMap` image, i.e. `overPullbackSnd (algebraMapOver B hA) Y.obj`
by `sourceBaseChangeAlgebraMap_obj`. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_separated_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    Separated Y.obj.hom ↔
      Separated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- Lemma 88.30.2 (4): with notation and assumptions as in Lemma 88.30.1, if
`f : X' ⟶ specOver hA` corresponds to `g : Y' ⟶ specOver (Spec.map (algebraMap A B) ≫ hA)`
via `sourceBaseChangeAlgebraMap`, then `f` is proper if and only if `g` is.
Here `f` is `Y.obj.hom` and `g` is the structure morphism of the
`sourceBaseChangeAlgebraMap` image, i.e. `overPullbackSnd (algebraMapOver B hA) Y.obj`
by `sourceBaseChangeAlgebraMap_obj`. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_proper_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    Proper Y.obj.hom ↔
      Proper ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- Lemma 88.30.2 (5): with notation and assumptions as in Lemma 88.30.1, if
`f : X' ⟶ specOver hA` corresponds to `g : Y' ⟶ specOver (Spec.map (algebraMap A B) ≫ hA)`
via `sourceBaseChangeAlgebraMap`, then `f` is finite if and only if `g` is.
Here `f` is `Y.obj.hom` and `g` is the structure morphism of the
`sourceBaseChangeAlgebraMap` image, i.e. `overPullbackSnd (algebraMapOver B hA) Y.obj`
by `sourceBaseChangeAlgebraMap_obj`. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_isFinite_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    IsFinite Y.obj.hom ↔
      IsFinite ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
