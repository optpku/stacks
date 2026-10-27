/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChange
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-! # Affine closed subsets and canonical base change -/

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong TopologicalSpace

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.zeroLocusPoints :
  ∀ {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S),
    Ideal A → Closeds (Points (specOver hA)))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.zeroLocusPoints_carrier :
  ∀ {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A),
    (zeroLocusPoints hA I : Set (Points (specOver hA))) =
      ofOver.pointsHomeomorph (Over.mk hA) ''
        (zeroLocusCloseds I : Set (Spec (.of A))))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.mem_zeroLocusPoints :
  ∀ {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) (x : Points (specOver hA)),
    x ∈ zeroLocusPoints hA I ↔
      (ofOver.pointsHomeomorph (Over.mk hA)).symm x ∈ zeroLocusCloseds I)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.zeroLocusPoints_preimage_algebraMapOver :
  ∀ {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A),
    (zeroLocusPoints hA I).preimage (Points.continuous_map (algebraMapOver B hA)) =
      zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
        (I.map (algebraMap A B)))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_mem :
  ∀ {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A)
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    locallyOfFiniteTypeIsoOverOpenProperty
      (openComplementι
        (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))
        (zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))))
      ((overPullback (algebraMapOver B hA)).obj Y.obj))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap :
  ∀ {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A),
    Source (specOver hA) (zeroLocusPoints hA I) ⥤
      Source (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))
        (zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_obj :
  ∀ {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj =
      Over.mk (overPullbackSnd (algebraMapOver B hA) Y.obj))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_hom :
  ∀ {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) {Y Y' : Source (specOver hA) (zeroLocusPoints hA I)}
    (φ : Y ⟶ Y'),
    ((sourceBaseChangeAlgebraMap B hA I).map φ).hom.left =
      overPullbackMap (algebraMapOver B hA) φ.hom)
