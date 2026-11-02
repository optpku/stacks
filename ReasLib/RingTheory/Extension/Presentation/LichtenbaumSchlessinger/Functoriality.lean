/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger
public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Explicit

/-!
# Functoriality of Lichtenbaum–Schlessinger complexes

A commutative square of algebras together with a factorization hom of polynomial
presentations, with a compatible map of relation indices, induces a cochain map
of Lichtenbaum–Schlessinger complexes after extension of scalars along `B → B'`.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open Algebra.Presentation
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

namespace Algebra.Presentation.LichtenbaumSchlessinger

variable {A B A' B' ι ι' σ τ : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A A' B'] [IsScalarTower A B B']

section RelationMaps

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- Coefficientwise application of a factorization hom, followed by the given map
of relation indices, as a map `F →+ F'`. -/
def mapFree (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ) : free P →+ free P' :=
  (Finsupp.mapDomain.addMonoidHom ρ).comp
    (Finsupp.mapRange.addMonoidHom f.toRingHom.toAddMonoidHom)

/-- `mapFree` sends a basis vector `single t p` to `single (ρ t) (f.toRingHom p)`. -/
theorem mapFree_single (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ) (t : σ) (p : P.Ring) :
    mapFree P P' f ρ (Finsupp.single t p) =
      Finsupp.single (ρ t) (f.toRingHom p) := by
  simp [mapFree] <;> rfl

/-- The identity map of a presentation acts identically on its free module. -/
theorem mapFree_refl (P : Presentation A B ι σ) :
    mapFree P P (.id P.toExtension) _root_.id = AddMonoidHom.id (free P) := by
  ext index coefficient
  simp [mapFree] <;> rfl

variable {A'' B'' ι'' υ : Type u} [CommRing A''] [CommRing B'']
  [Algebra A'' B''] [Algebra A' A''] [Algebra B' B'']
  [Algebra A A''] [Algebra B B'']
  [IsScalarTower A A' A''] [IsScalarTower B B' B''] in
/-- Free-module comparisons compose along the composite relation-index map. -/
theorem mapFree_comp (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (P'' : Presentation A'' B'' ι'' υ)
    (f : P.toExtension.Hom P'.toExtension) (g : P'.toExtension.Hom P''.toExtension)
    (ρ : σ → τ) (ρ' : τ → υ) :
    mapFree P P'' (g.comp f) (ρ' ∘ ρ) =
      (mapFree P' P'' g ρ').comp (mapFree P P' f ρ) := by
  ext index coefficient
  simp [mapFree] <;> rfl

/-- `mapFree` is semilinear on basis vectors with respect to the factorization hom. -/
theorem mapFree_smul_single (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (r : P.Ring) (t : σ) :
    mapFree P P' f ρ (r • Finsupp.single t (1 : P.Ring)) =
      Finsupp.single (ρ t) (f.toRingHom r) := sorry

/-- If the original relations are sent to the specified target relations, then
`mapFree` preserves `Rel`. -/
theorem mapFree_mem_rel (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t))
    {x : free P} (hx : x ∈ rel P) : mapFree P P' f ρ x ∈ rel P' := sorry

/-- If the original relations are sent to the specified target relations, then
`mapFree` preserves trivial relations. -/
theorem mapFree_mem_trivialRel (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t))
    {x : free P} (hx : x ∈ trivialRel P) : mapFree P P' f ρ x ∈ trivialRel P' := sorry

/-- The induced map on relation modules `Rel →+ Rel'`. -/
def mapRel (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    rel P →+ rel P' where
  toFun x := ⟨mapFree P P' f ρ (x : free P), mapFree_mem_rel P P' f ρ h_rel x.property⟩
  map_zero' := sorry
  map_add' := sorry

/-- Unfolding of `mapRel` on the underlying free modules. -/
theorem mapRel_apply (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) (x : rel P) :
    (mapRel P P' f ρ h_rel x : free P') = mapFree P P' f ρ (x : free P) := sorry

/-- `mapRel` sends the submodule of trivial relations into the corresponding
submodule for `P'`. -/
theorem mapRel_map_trivialRel (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    ((trivialRel P).comap (rel P).subtype).toAddSubgroup ≤
      AddSubgroup.comap (mapRel P P' f ρ h_rel)
        ((trivialRel P').comap (rel P').subtype).toAddSubgroup := sorry

/-- The induced map on `Rel / TrivRel`. -/
def mapRelModTrivial (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    relModTrivial P →+ relModTrivial P' :=
  QuotientAddGroup.map
    ((trivialRel P).comap (rel P).subtype).toAddSubgroup
    ((trivialRel P').comap (rel P').subtype).toAddSubgroup
    (mapRel P P' f ρ h_rel) (mapRel_map_trivialRel P P' f ρ h_rel)

/-- `mapRelModTrivial` sends the class of a relation to the class of its image. -/
theorem mapRelModTrivial_mk (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) (x : rel P) :
    mapRelModTrivial P P' f ρ h_rel (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mapRel P P' f ρ h_rel x) := sorry

end RelationMaps

/-- Degree-`0` comparison on cotangent spaces, as a map of `B`-modules into the
restriction of scalars of `P'.toExtension.CotangentSpace`. -/
def mapCotangentSpaceRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) :
    ModuleCat.of B P.toExtension.CotangentSpace ⟶
      (ModuleCat.restrictScalars (algebraMap B B')).obj
        (ModuleCat.of B' P'.toExtension.CotangentSpace) :=
  -- Local instance justification (defeq pin): restrictScalars uses Module.compHom along algebraMap B B'.
  letI : Module B P'.toExtension.CotangentSpace :=
    Module.compHom _ (algebraMap B B')
  ModuleCat.ofHom
    { toFun := Algebra.Extension.CotangentSpace.map f
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`0` cochain component: the scalar extension of `CotangentSpace.map`
along `algebraMap B B'`. -/
def mapCotangentSpace (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B P.toExtension.CotangentSpace) ⟶
      ModuleCat.of B' P'.toExtension.CotangentSpace :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapCotangentSpaceRestrict P P' f)

/-- Unfolding of `mapCotangentSpace` through the extension-restriction adjunction. -/
theorem mapCotangentSpace_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) :
    mapCotangentSpace P P' f =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapCotangentSpaceRestrict P P' f) := sorry

/-- On pure tensors, the degree-`0` comparison sends `s ⊗ₜ D p` to
`algebraMap B B' s ⊗ₜ D (f.toRingHom p)`. -/
theorem mapCotangentSpace_tmul (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension)
    (s : B) (p : P.toExtension.Ring) :
    (mapCotangentSpace P P' f).hom
        ((1 : B') ⊗ₜ[B, algebraMap B B']
          (s ⊗ₜ[P.toExtension.Ring] KaehlerDifferential.D A P.toExtension.Ring p)) =
      algebraMap B B' s ⊗ₜ[P'.toExtension.Ring]
        KaehlerDifferential.D A' P'.toExtension.Ring (f.toRingHom p) := sorry

/-- Degree-`-1` comparison on `F ⊗ B`, as a map of `B`-modules into the restriction
of scalars of `F' ⊗ B'`. -/
def mapFreeTensorRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ) :
    ModuleCat.of B (B ⊗[P.Ring] free P) ⟶
      (ModuleCat.restrictScalars (algebraMap B B')).obj
        (ModuleCat.of B' (B' ⊗[P'.Ring] free P')) :=
  -- Local instance justification (noncanonical choice): Algebra P.Ring B' is the chosen composite P.Ring → B → B'.
  letI := ((algebraMap B B').comp (algebraMap P.Ring B)).toAlgebra
  -- Local instance justification (defeq pin): the tower P.Ring → B → B' is this composite.
  letI : IsScalarTower P.Ring B B' := IsScalarTower.of_algebraMap_eq' rfl
  -- Local instance justification (defeq pin): restrictScalars uses Module.compHom along algebraMap B B'.
  letI : Module B (B' ⊗[P'.Ring] free P') := Module.compHom _ (algebraMap B B')
  ModuleCat.ofHom
    { toFun :=
        (_root_.TensorProduct.lift)
          (LinearMap.mk₂ P.Ring
            (fun (b : B) (m : free P) ↦ algebraMap B B' b ⊗ₜ[P'.Ring] mapFree P P' f ρ m)
            sorry sorry sorry sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`-1` cochain component after extension of scalars along `algebraMap B B'`. -/
def mapFreeTensor (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B (B ⊗[P.Ring] free P)) ⟶
      ModuleCat.of B' (B' ⊗[P'.Ring] free P') :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapFreeTensorRestrict P P' f ρ)

/-- Unfolding of `mapFreeTensor` through the extension-restriction adjunction. -/
theorem mapFreeTensor_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ) :
    mapFreeTensor P P' f ρ =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapFreeTensorRestrict P P' f ρ) := sorry

/-- The scalar-extended free-module comparison on pure tensors. -/
theorem mapFreeTensor_tmul (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (scalar : B') (coefficient : B) (vector : free P) :
    (mapFreeTensor P P' f ρ).hom
        (scalar ⊗ₜ[B, algebraMap B B'] (coefficient ⊗ₜ[P.Ring] vector)) =
      scalar • (algebraMap B B' coefficient ⊗ₜ[P'.Ring] mapFree P P' f ρ vector) := sorry

/-- Degree-`-2` comparison on `S ⊗ Rel/TrivRel`, as a map of `B`-modules into the
restriction of scalars of the corresponding `P'` term. -/
def mapRelModTrivialTensorRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    ModuleCat.of B (B ⊗[P.Ring] relModTrivial P) ⟶
      (ModuleCat.restrictScalars (algebraMap B B')).obj
        (ModuleCat.of B' (B' ⊗[P'.Ring] relModTrivial P')) :=
  -- Local instance justification (noncanonical choice): Algebra P.Ring B' is the chosen composite P.Ring → B → B'.
  letI := ((algebraMap B B').comp (algebraMap P.Ring B)).toAlgebra
  -- Local instance justification (defeq pin): the tower P.Ring → B → B' is this composite.
  letI : IsScalarTower P.Ring B B' := IsScalarTower.of_algebraMap_eq' rfl
  -- Local instance justification (defeq pin): restrictScalars uses Module.compHom along algebraMap B B'.
  letI : Module B (B' ⊗[P'.Ring] relModTrivial P') := Module.compHom _ (algebraMap B B')
  ModuleCat.ofHom
    { toFun :=
        (_root_.TensorProduct.lift)
          (LinearMap.mk₂ P.Ring
            (fun (b : B) (x : relModTrivial P) ↦
              algebraMap B B' b ⊗ₜ[P'.Ring] mapRelModTrivial P P' f ρ h_rel x)
            sorry sorry sorry sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`-2` cochain component after extension of scalars along `algebraMap B B'`. -/
def mapRelModTrivialTensor (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B (B ⊗[P.Ring] relModTrivial P)) ⟶
      ModuleCat.of B' (B' ⊗[P'.Ring] relModTrivial P') :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapRelModTrivialTensorRestrict P P' f ρ h_rel)

/-- Unfolding of `mapRelModTrivialTensor` through the extension-restriction adjunction. -/
theorem mapRelModTrivialTensor_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    mapRelModTrivialTensor P P' f ρ h_rel =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapRelModTrivialTensorRestrict P P' f ρ h_rel) := sorry

/-- Components of the cochain map of Lichtenbaum–Schlessinger complexes. -/
def map_f (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    ∀ i : ℤ,
      (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (complex P)).X i ⟶
        (complex P').X i
  | Int.ofNat 0 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_zero P).hom ≫
        mapCotangentSpace P P' f ≫ (complex_X_zero P').inv
  | Int.negSucc 0 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negOne P).hom ≫
        mapFreeTensor P P' f ρ ≫ (complex_X_negOne P').inv
  | Int.negSucc 1 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negTwo P).hom ≫
        mapRelModTrivialTensor P P' f ρ h_rel ≫ (complex_X_negTwo P').inv
  | Int.negSucc (_n + 2) => 0
  | Int.ofNat (_n + 1) => 0

/-- The cochain map of Lichtenbaum–Schlessinger complexes induced by a commutative
square of algebras and a compatible map of relation indices. -/
def map (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complex P) ⟶
      complex P' where
  f := map_f P P' f ρ h_rel
  comm' := sorry

/-- Unfolding of the components of `map`. -/
theorem map_f_eq (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) (i : ℤ) :
    (map P P' f ρ h_rel).f i = map_f P P' f ρ h_rel i := sorry

/-- Degree `0` of `map` is `mapCotangentSpace` after the degree-`0` identifications. -/
theorem map_f_zero (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    (map P P' f ρ h_rel).f 0 =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_zero P).hom ≫
        mapCotangentSpace P P' f ≫ (complex_X_zero P').inv := sorry

/-- Degree `-1` of `map` is `mapFreeTensor` after the degree-`-1` identifications. -/
theorem map_f_negOne (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    (map P P' f ρ h_rel).f (-1) =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negOne P).hom ≫
        mapFreeTensor P P' f ρ ≫ (complex_X_negOne P').inv := sorry

/-- Degree `-2` of `map` is `mapRelModTrivialTensor` after the degree-`-2`
identifications. -/
theorem map_f_negTwo (P : Presentation A B ι σ) (P' : Presentation A' B' ι' τ)
    (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    (map P P' f ρ h_rel).f (-2) =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negTwo P).hom ≫
        mapRelModTrivialTensor P P' f ρ h_rel ≫ (complex_X_negTwo P').inv := sorry

/-- The identity comparison agrees degreewise with the canonical scalar-unit map. -/
theorem map_refl_f (P : Presentation A B ι σ) (degree : ℤ) :
    (map P P (.id P.toExtension) _root_.id (fun _ => rfl)).f degree =
      (ModuleCat.extendScalarsId B).hom.app ((complex P).X degree) := sorry

section Composition

variable {A'' B'' ι'' υ : Type u} [CommRing A''] [CommRing B'']
variable [Algebra A'' B''] [Algebra A' A''] [Algebra B' B'']
variable [Algebra A A''] [Algebra B B'']
variable [IsScalarTower A A' A''] [IsScalarTower B B' B'']
variable [Algebra A' B''] [Algebra A B'']
variable [IsScalarTower A' A'' B''] [IsScalarTower A' B' B'']
variable [IsScalarTower A A'' B''] [IsScalarTower A B B'']

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
  [Algebra A' B''] [Algebra A B''] [IsScalarTower A' A'' B'']
  [IsScalarTower A' B' B''] [IsScalarTower A A'' B''] [IsScalarTower A B B''] in
/-- Quotient comparisons compose with the given relation-index maps. -/
theorem mapRelModTrivial_comp (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (P'' : Presentation A'' B'' ι'' υ)
    (f : P.toExtension.Hom P'.toExtension) (g : P'.toExtension.Hom P''.toExtension)
    (ρ : σ → τ) (ρ' : τ → υ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t))
    (h_rel' : ∀ t, g.toRingHom (P'.relation t) = P''.relation (ρ' t)) :
    mapRelModTrivial P P'' (g.comp f) (ρ' ∘ ρ)
        (fun t => (congrArg g.toRingHom (h_rel t)).trans (h_rel' (ρ t))) =
      (mapRelModTrivial P' P'' g ρ' h_rel').comp
        (mapRelModTrivial P P' f ρ h_rel) := sorry

/-- Complex comparisons compose degreewise via the canonical scalar-extension associator. -/
theorem map_comp_f (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (P'' : Presentation A'' B'' ι'' υ)
    (f : P.toExtension.Hom P'.toExtension) (g : P'.toExtension.Hom P''.toExtension)
    (ρ : σ → τ) (ρ' : τ → υ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t))
    (h_rel' : ∀ t, g.toRingHom (P'.relation t) = P''.relation (ρ' t)) (degree : ℤ) :
    (map P P'' (g.comp f) (ρ' ∘ ρ)
        (fun t => (congrArg g.toRingHom (h_rel t)).trans (h_rel' (ρ t)))).f degree =
      eqToHom (congrArg (fun ringHom : B →+* B'' =>
        (ModuleCat.extendScalars ringHom).obj ((complex P).X degree))
          (IsScalarTower.algebraMap_eq B B' B'')) ≫
        (ModuleCat.extendScalarsComp (algebraMap B B') (algebraMap B' B'')).hom.app
          ((complex P).X degree) ≫
        (ModuleCat.extendScalars (algebraMap B' B'')).map
          ((map P P' f ρ h_rel).f degree) ≫
        (map P' P'' g ρ' h_rel').f degree := sorry

end Composition

end Algebra.Presentation.LichtenbaumSchlessinger

namespace Algebra.Presentation.LichtenbaumSchlessinger

variable {A B A' B' ι ι' σ τ : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- The two paths around a commutative square of algebra maps agree. -/
theorem algebraMap_comp :
    (algebraMap A' B').comp (algebraMap A A') =
      (algebraMap B B').comp (algebraMap A B) := sorry

/-- The comparison maps `toComplex` fit in a commutative square in the derived
category with the induced map of Lichtenbaum–Schlessinger complexes and
cotangent-complex functoriality. -/
theorem comparison_commSq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    CommSq
      (DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (toComplex P)))
      (DerivedCategory.Q.map
        (Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
          (algebraMap A A') (algebraMap B B') algebraMap_comp))
      (DerivedCategory.Q.map (map P P' f ρ h_rel))
      (DerivedCategory.Q.map (toComplex P')) := sorry

/-- The two composites around the derived comparison square agree. -/
theorem comparison_commSq_w (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' τ) (f : P.toExtension.Hom P'.toExtension) (ρ : σ → τ)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (ρ t)) :
    DerivedCategory.Q.map
          (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (toComplex P)) ≫
        DerivedCategory.Q.map (map P P' f ρ h_rel) =
      DerivedCategory.Q.map
          (Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
            (algebraMap A A') (algebraMap B B') algebraMap_comp) ≫
        DerivedCategory.Q.map (toComplex P') := sorry

end Algebra.Presentation.LichtenbaumSchlessinger
