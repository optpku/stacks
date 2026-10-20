/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Objects
public import ReasLib.RingTheory.RingHom.IndEtale.Composition

@[expose] public section

open CategoryTheory
noncomputable section
universe u

namespace CommAlgCat.IndEtale

/-- Transport the `R`-algebra structure along a ring equivalence `R ≃+* S`. -/
@[reducible]
def algebraCompRingEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (A : Type u) [CommRing A] [Algebra R A] : Algebra S A :=
  ((algebraMap R A).comp e.symm.toRingHom).toAlgebra

/-- The structure map of `algebraCompRingEquiv` is `algebraMap R A` after `e.symm`. -/
theorem algebraCompRingEquiv_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (A : Type u) [CommRing A] [Algebra R A] :
    @algebraMap S A _ _ (algebraCompRingEquiv e A) =
      (algebraMap R A).comp e.symm.toRingHom := rfl

/-- An `R`-algebra map remains an `S`-algebra map after `algebraCompRingEquiv`. -/
def reindexAlgHom {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    @AlgHom S A B _ _ _ (algebraCompRingEquiv e A) (algebraCompRingEquiv e B) :=
  @AlgHom.mk S A B _ _ _ (algebraCompRingEquiv e A) (algebraCompRingEquiv e B)
    f.toRingHom (fun s ↦ f.commutes (e.symm s))

/-- Reindexing along a ring equivalence preserves ind-étaleness. -/
theorem reindex_obj_indEtale {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (C : IndEtale.{u} R) :
    (@algebraMap S C _ _ (algebraCompRingEquiv e C)).IndEtale :=
  RingHom.IndEtale.comp e.symm.toRingHom (algebraMap R C)
    (RingHom.IndEtale.ofBijective _ e.symm.bijective) C.property

/-- Reindex ind-étale algebras along a ring equivalence, keeping the same carrier. -/
def reindex {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IndEtale.{u} R ⥤ IndEtale.{u} S where
  obj C :=
    @of S _ C _ (algebraCompRingEquiv e C) (reindex_obj_indEtale e C)
  map {C D} f :=
    @ofHom S _ C D _ _ (algebraCompRingEquiv e C) (algebraCompRingEquiv e D)
      (reindex_obj_indEtale e C) (reindex_obj_indEtale e D)
      (reindexAlgHom e f.hom.hom)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Reindexing sends an algebra to the same carrier with transported scalars. -/
theorem reindex_obj {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (C : IndEtale.{u} R) :
    ((reindex e).obj C).obj = @CommAlgCat.of S _ C _ (algebraCompRingEquiv e C) :=
  rfl

/-- Reindexing scalars is fully faithful, with inverse transport on algebra maps. -/
def reindexFullyFaithful {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (reindex e).FullyFaithful where
  preimage {C D} f :=
    ObjectProperty.homMk (CommAlgCat.ofHom (show C →ₐ[R] D from
      { toRingHom := f.hom.hom.toRingHom
        commutes' := by
          intro r
          have h := f.hom.hom.commutes (e r)
          change f.hom.hom (algebraMap R C (e.symm (e r))) =
            algebraMap R D (e.symm (e r)) at h
          rw [e.symm_apply_apply] at h
          change f.hom.hom (algebraMap R C r) = algebraMap R D r
          exact h }))
  map_preimage := by intro C D f; ext; rfl
  preimage_map := by intro C D f; ext; rfl

end CommAlgCat.IndEtale

