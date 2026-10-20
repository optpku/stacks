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
public import stacks_project.Chap92.«92_13_0_1_Complex»

/-!
# Functoriality of Lichtenbaum–Schlessinger complexes

A commutative square of algebras together with a factorization hom of polynomial
presentations, with relation indices extended along `σ ⊕ τ`, induces a cochain map
of Lichtenbaum–Schlessinger complexes after extension of scalars along `B → B'`.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

namespace Algebra.Presentation.LichtenbaumSchlessinger

variable {A B A' B' ι ι' σ τ : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- Coefficientwise application of a factorization hom, followed by the coproduct
inclusion of relation indices, as a map `F →+ F'`. -/
def mapFree (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension) : free P →+ free P' :=
  (Finsupp.mapDomain.addMonoidHom Sum.inl).comp
    (Finsupp.mapRange.addMonoidHom f.toRingHom.toAddMonoidHom)

/-- `mapFree` sends a basis vector `single t p` to `single (Sum.inl t) (f.toRingHom p)`. -/
theorem mapFree_single (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension) (t : σ) (p : P.Ring) :
    mapFree P P' f (Finsupp.single t p) =
      Finsupp.single (Sum.inl t) (f.toRingHom p) := sorry

/-- `mapFree` is semilinear on basis vectors with respect to the factorization hom. -/
theorem mapFree_smul_single (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (r : P.Ring) (t : σ) :
    mapFree P P' f (r • Finsupp.single t (1 : P.Ring)) =
      Finsupp.single (Sum.inl t) (f.toRingHom r) := sorry

/-- If the original relations are sent to the coproduct-summand relations, then
`mapFree` preserves `Rel`. -/
theorem mapFree_mem_rel (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t))
    {x : free P} (hx : x ∈ rel P) : mapFree P P' f x ∈ rel P' := sorry

/-- If the original relations are sent to the coproduct-summand relations, then
`mapFree` preserves trivial relations. -/
theorem mapFree_mem_trivialRel (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t))
    {x : free P} (hx : x ∈ trivialRel P) : mapFree P P' f x ∈ trivialRel P' := sorry

/-- The induced map on relation modules `Rel →+ Rel'`. -/
def mapRel (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    rel P →+ rel P' where
  toFun x := ⟨mapFree P P' f (x : free P), mapFree_mem_rel P P' f h_rel x.property⟩
  map_zero' := sorry
  map_add' := sorry

/-- Unfolding of `mapRel` on the underlying free modules. -/
theorem mapRel_apply (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) (x : rel P) :
    (mapRel P P' f h_rel x : free P') = mapFree P P' f (x : free P) := sorry

/-- `mapRel` sends the submodule of trivial relations into the corresponding
submodule for `P'`. -/
theorem mapRel_map_trivialRel (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    ((trivialRel P).comap (rel P).subtype).toAddSubgroup ≤
      AddSubgroup.comap (mapRel P P' f h_rel)
        ((trivialRel P').comap (rel P').subtype).toAddSubgroup := sorry

/-- The induced map on `Rel / TrivRel`. -/
def mapRelModTrivial (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    relModTrivial P →+ relModTrivial P' :=
  QuotientAddGroup.map
    ((trivialRel P).comap (rel P).subtype).toAddSubgroup
    ((trivialRel P').comap (rel P').subtype).toAddSubgroup
    (mapRel P P' f h_rel) (mapRel_map_trivialRel P P' f h_rel)

/-- `mapRelModTrivial` sends the class of a relation to the class of its image. -/
theorem mapRelModTrivial_mk (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) (x : rel P) :
    mapRelModTrivial P P' f h_rel (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mapRel P P' f h_rel x) := sorry

/-- Degree-`0` comparison on cotangent spaces, as a map of `B`-modules into the
restriction of scalars of `P'.toExtension.CotangentSpace`. -/
def mapCotangentSpaceRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension) :
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
def mapCotangentSpace (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B P.toExtension.CotangentSpace) ⟶
      ModuleCat.of B' P'.toExtension.CotangentSpace :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapCotangentSpaceRestrict P P' f)

/-- Unfolding of `mapCotangentSpace` through the extension-restriction adjunction. -/
theorem mapCotangentSpace_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension) :
    mapCotangentSpace P P' f =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapCotangentSpaceRestrict P P' f) := sorry

/-- On pure tensors, the degree-`0` comparison sends `s ⊗ₜ D p` to
`algebraMap B B' s ⊗ₜ D (f.toRingHom p)`. -/
theorem mapCotangentSpace_tmul (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (s : B) (p : P.toExtension.Ring) :
    (mapCotangentSpace P P' f).hom
        ((1 : B') ⊗ₜ[B, algebraMap B B']
          (s ⊗ₜ[P.toExtension.Ring] KaehlerDifferential.D A P.toExtension.Ring p)) =
      algebraMap B B' s ⊗ₜ[P'.toExtension.Ring]
        KaehlerDifferential.D A' P'.toExtension.Ring (f.toRingHom p) := sorry

/-- Degree-`-1` comparison on `F ⊗ B`, as a map of `B`-modules into the restriction
of scalars of `F' ⊗ B'`. -/
def mapFreeTensorRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension) :
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
            (fun (b : B) (m : free P) ↦ algebraMap B B' b ⊗ₜ[P'.Ring] mapFree P P' f m)
            sorry sorry sorry sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`-1` cochain component after extension of scalars along `algebraMap B B'`. -/
def mapFreeTensor (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B (B ⊗[P.Ring] free P)) ⟶
      ModuleCat.of B' (B' ⊗[P'.Ring] free P') :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapFreeTensorRestrict P P' f)

/-- Unfolding of `mapFreeTensor` through the extension-restriction adjunction. -/
theorem mapFreeTensor_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension) :
    mapFreeTensor P P' f =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapFreeTensorRestrict P P' f) := sorry

/-- Degree-`-2` comparison on `S ⊗ Rel/TrivRel`, as a map of `B`-modules into the
restriction of scalars of the corresponding `P'` term. -/
def mapRelModTrivialTensorRestrict (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
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
              algebraMap B B' b ⊗ₜ[P'.Ring] mapRelModTrivial P P' f h_rel x)
            sorry sorry sorry sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`-2` cochain component after extension of scalars along `algebraMap B B'`. -/
def mapRelModTrivialTensor (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    (ModuleCat.extendScalars (algebraMap B B')).obj
        (ModuleCat.of B (B ⊗[P.Ring] relModTrivial P)) ⟶
      ModuleCat.of B' (B' ⊗[P'.Ring] relModTrivial P') :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
    (mapRelModTrivialTensorRestrict P P' f h_rel)

/-- Unfolding of `mapRelModTrivialTensor` through the extension-restriction adjunction. -/
theorem mapRelModTrivialTensor_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    mapRelModTrivialTensor P P' f h_rel =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B B')).homEquiv _ _).symm
        (mapRelModTrivialTensorRestrict P P' f h_rel) := sorry

/-- Components of the cochain map of Lichtenbaum–Schlessinger complexes. -/
def map_f (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    ∀ i : ℤ,
      (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (complex P)).X i ⟶
        (complex P').X i
  | Int.ofNat 0 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_zero P).hom ≫
        mapCotangentSpace P P' f ≫ (complex_X_zero P').inv
  | Int.negSucc 0 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negOne P).hom ≫
        mapFreeTensor P P' f ≫ (complex_X_negOne P').inv
  | Int.negSucc 1 =>
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negTwo P).hom ≫
        mapRelModTrivialTensor P P' f h_rel ≫ (complex_X_negTwo P').inv
  | Int.negSucc (_n + 2) => 0
  | Int.ofNat (_n + 1) => 0

/-- The cochain map of Lichtenbaum–Schlessinger complexes induced by a commutative
square of algebras and a coproduct relation-extension of polynomial presentations. -/
def map (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complex P) ⟶
      complex P' where
  f := map_f P P' f h_rel
  comm' := sorry

/-- Unfolding of the components of `map`. -/
theorem map_f_eq (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) (i : ℤ) :
    (map P P' f h_rel).f i = map_f P P' f h_rel i := sorry

/-- Degree `0` of `map` is `mapCotangentSpace` after the degree-`0` identifications. -/
theorem map_f_zero (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    (map P P' f h_rel).f 0 =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_zero P).hom ≫
        mapCotangentSpace P P' f ≫ (complex_X_zero P').inv := sorry

/-- Degree `-1` of `map` is `mapFreeTensor` after the degree-`-1` identifications. -/
theorem map_f_negOne (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    (map P P' f h_rel).f (-1) =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negOne P).hom ≫
        mapFreeTensor P P' f ≫ (complex_X_negOne P').inv := sorry

/-- Degree `-2` of `map` is `mapRelModTrivialTensor` after the degree-`-2`
identifications. -/
theorem map_f_negTwo (P : Presentation A B ι σ) (P' : Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    (map P P' f h_rel).f (-2) =
      (ModuleCat.extendScalars (algebraMap B B')).map (complex_X_negTwo P).hom ≫
        mapRelModTrivialTensor P P' f h_rel ≫ (complex_X_negTwo P').inv := sorry

end Algebra.Presentation.LichtenbaumSchlessinger
