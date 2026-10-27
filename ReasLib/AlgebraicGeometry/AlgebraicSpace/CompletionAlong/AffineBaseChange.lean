/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap

/-!
# Affine base change away from a closed subset

Algebra-map base change acts on locally finite type morphisms that are
isomorphisms away from an affine closed subset. It is an equivalence when
the canonical map on adic completions is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The closed subset `V(I) ⊆ |Spec(A)|`, as a closed set of points of the
algebraic space `specOver hA`. -/
def zeroLocusPoints {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) : Closeds (Points (specOver hA)) :=
  (zeroLocusCloseds I).preimage (ofOver.pointsHomeomorph (Over.mk hA)).symm.continuous

/-- The carrier of `zeroLocusPoints hA I` is the image of `V(I)` under the
homeomorphism from scheme points of `Spec(A)` to points of `specOver hA`. -/
theorem zeroLocusPoints_carrier {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    (zeroLocusPoints hA I : Set (Points (specOver hA))) =
      ofOver.pointsHomeomorph (Over.mk hA) ''
        (zeroLocusCloseds I : Set (Spec (.of A))) :=
  sorry

/-- A point of `specOver hA` lies in `zeroLocusPoints hA I` if and only if its
scheme-point preimage lies in `V(I)`. -/
theorem mem_zeroLocusPoints {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) (x : Points (specOver hA)) :
    x ∈ zeroLocusPoints hA I ↔
      (ofOver.pointsHomeomorph (Over.mk hA)).symm x ∈ zeroLocusCloseds I :=
  sorry

/-- Inverse image of `V(I)` along `Spec(B) ⟶ Spec(A)` is `V(IB)`. -/
theorem zeroLocusPoints_preimage_algebraMapOver {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    (zeroLocusPoints hA I).preimage (Points.continuous_map (algebraMapOver B hA)) =
      zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
        (I.map (algebraMap A B)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Base change along `algebraMapOver B hA` preserves being locally of finite
type and an isomorphism over the complementary open of `V(IB)`. -/
theorem sourceBaseChangeAlgebraMap_mem {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A)
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    locallyOfFiniteTypeIsoOverOpenProperty
      (openComplementι
        (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))
        (zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))))
      ((overPullback (algebraMapOver B hA)).obj Y.obj) :=
  sorry

/-- Base change along `algebraMapOver B hA` on locally finite type morphisms
that are isomorphisms away from `V(I)`, with target complement `V(IB)`. -/
def sourceBaseChangeAlgebraMap {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Source (specOver hA) (zeroLocusPoints hA I) ⥤
      Source (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))
        (zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))) :=
  ObjectProperty.lift
    (locallyOfFiniteTypeIsoOverOpenProperty
      (openComplementι
        (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))
        (zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B)))))
    (LocallyOfFiniteTypeIsoOverOpen.inclusion
        (openComplementι (specOver hA) (zeroLocusPoints hA I)) ⋙
      overPullback (algebraMapOver B hA))
    (fun Y ↦ sourceBaseChangeAlgebraMap_mem B hA I Y)

/-- After inclusion into the slice, `sourceBaseChangeAlgebraMap` is ordinary
slice base change along `algebraMapOver B hA`. -/
theorem sourceBaseChangeAlgebraMap_obj {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj =
      Over.mk (overPullbackSnd (algebraMapOver B hA) Y.obj) :=
  sorry

/-- On morphisms, `sourceBaseChangeAlgebraMap` is the induced map of fibre
products along `algebraMapOver B hA`. -/
theorem sourceBaseChangeAlgebraMap_hom {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) {Y Y' : Source (specOver hA) (zeroLocusPoints hA I)}
    (φ : Y ⟶ Y') :
    ((sourceBaseChangeAlgebraMap B hA I).map φ).hom.left =
      overPullbackMap (algebraMapOver B hA) φ.hom :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, base change is an equivalence on locally finite type morphisms
that are isomorphisms away from the closed subsets defined by the ideals. -/
theorem isEquivalence_sourceBaseChangeAlgebraMap {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B)) :
    (sourceBaseChangeAlgebraMap B hA I).IsEquivalence :=
  sorry


/-- Bijectivity of the canonical completion map makes affine base change an
equivalence on locally finite type morphisms isomorphic away from the ideal. -/
instance instIsEquivalenceSourceBaseChangeAlgebraMap {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    [Fact (Function.Bijective
      (AdicCompletion.extensionMap I :
        AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))] :
    (sourceBaseChangeAlgebraMap B hA I).IsEquivalence :=
  isEquivalence_sourceBaseChangeAlgebraMap B hA I Fact.out

end AlgebraicGeometry.AlgebraicSpace.completionAlong
