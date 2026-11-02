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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
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
  ((ofOver.pointsHomeomorph (Over.mk hA)).image_eq_preimage_symm
    (zeroLocusCloseds I : Set (Spec (.of A)))).symm

/-- A point of `specOver hA` lies in `zeroLocusPoints hA I` if and only if its
scheme-point preimage lies in `V(I)`. -/
theorem mem_zeroLocusPoints {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) (x : Points (specOver hA)) :
    x ∈ zeroLocusPoints hA I ↔
      (ofOver.pointsHomeomorph (Over.mk hA)).symm x ∈ zeroLocusCloseds I :=
  Iff.rfl

/-- Inverse image of `V(I)` along `Spec(B) ⟶ Spec(A)` is `V(IB)`. -/
theorem zeroLocusPoints_preimage_algebraMapOver {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    (zeroLocusPoints hA I).preimage (Points.continuous_map (algebraMapOver B hA)) =
      zeroLocusPoints (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
        (I.map (algebraMap A B)) := by
  ext x
  obtain ⟨y, rfl⟩ :=
    (ofOver.pointsHomeomorph
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA))).surjective x
  let f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA) ⟶
      Over.mk hA := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) rfl
  change (ofOver.pointsEquiv (Over.mk hA)).symm
      (Points.map (ofOverMap f) (ofOver.pointsEquiv _ y)) ∈ zeroLocusCloseds I ↔
    (ofOver.pointsEquiv _).symm (ofOver.pointsEquiv _ y) ∈
      zeroLocusCloseds (I.map (algebraMap A B))
  rw [← ofOver.pointsEquiv_naturality f y, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  change I ≤ y.asIdeal.comap (algebraMap A B) ↔ I.map (algebraMap A B) ≤ y.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

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
  by
    rw [← zeroLocusPoints_preimage_algebraMapOver hA I]
    let f := algebraMapOver B hA
    let T := zeroLocusPoints hA I
    let ι := openComplementι (specOver hA) T
    let ι' := openComplementι _ (T.preimage (Points.continuous_map f))
    change LocallyOfFiniteType (overPullbackSnd f Y.obj) ∧
      IsIso (openInverseImageTo (overPullbackSnd f Y.obj) ι')
    refine ⟨LocallyOfFiniteType.of_isPullback
      (ReasLibPullback.isPullback Y.obj.hom f) Y.property.1, ?_⟩
    have hrange : Set.range (Points.map (ι' ≫ f)) ⊆ (T.compl : Set _) := by
      rintro _ ⟨x, rfl⟩
      rw [Points.map_comp]
      have hx : Points.map ι' x ∈ Set.range (Points.map ι') := ⟨x, rfl⟩
      rw [openComplementAlong_pointsSet] at hx
      exact hx
    let j := OpenSubspace.Construction.lift (W := T.compl) (ι' ≫ f) hrange
    have hj : j ≫ ι = ι' ≫ f := OpenSubspace.Construction.lift_ι _ _
    let q := openInverseImageι (overPullbackSnd f Y.obj) ι'
    let p := openInverseImageTo (overPullbackSnd f Y.obj) ι'
    have outer : IsPullback (q ≫ overPullbackFst f Y.obj) p Y.obj.hom (j ≫ ι) := by
      rw [hj]
      exact (openInverseImage_isPullback (overPullbackSnd f Y.obj) ι').paste_horiz
        (ReasLibPullback.isPullback Y.obj.hom f)
    let sq := openInverseImage_isPullback Y.obj.hom ι
    let k := sq.lift (q ≫ overPullbackFst f Y.obj) (p ≫ j)
      (by simpa only [Category.assoc] using outer.w)
    have hk₁ : k ≫ openInverseImageι Y.obj.hom ι = q ≫ overPullbackFst f Y.obj :=
      sq.lift_fst _ _ _
    have hk₂ : k ≫ openInverseImageTo Y.obj.hom ι = p ≫ j := sq.lift_snd _ _ _
    have hs : IsPullback k p (openInverseImageTo Y.obj.hom ι) j :=
      IsPullback.of_right (by rw [hk₁]; exact outer) hk₂ sq
    letI : IsIso (openInverseImageTo Y.obj.hom ι) := Y.property.2
    exact hs.isIso_snd_of_isIso

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
  rfl

/-- On morphisms, `sourceBaseChangeAlgebraMap` is the induced map of fibre
products along `algebraMapOver B hA`. -/
theorem sourceBaseChangeAlgebraMap_hom {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) {Y Y' : Source (specOver hA) (zeroLocusPoints hA I)}
    (φ : Y ⟶ Y') :
    ((sourceBaseChangeAlgebraMap B hA I).map φ).hom.left =
      overPullbackMap (algebraMapOver B hA) φ.hom :=
  rfl

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
