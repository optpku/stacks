/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Set.Finite.Basic
public import ReasLib.Algebra.IndEtaleEnvelope.Presentation
public import ReasLib.CategoryTheory.Limits.ChangeOfIndex

/-!
# The ind-étale envelope `T(A)`

`T(A)` is the directed colimit of the finite-stage tensors `B_E` of
faithfully flat standard-smooth presentations of relative dimension 0.
A ring map `φ : A →+* A'` acts by coefficient pushforward on presentations,
sends finite stages `B_E` to `B_{φ(E)}`, and induces `T(A) →+* T(A')` by
the colimit comparison associated to the resulting natural transformation.
-/

@[expose] public section

universe u

open Algebra CategoryTheory Limits CommRingCat MvPolynomial
open Algebra.IndEtaleEnvelope

namespace Algebra.IndEtaleEnvelope

variable {A : Type u} [CommRing A]

/-- The directed index poset `I(A)` of finite subsets of `S(A)`. -/
abbrev Index (A : Type u) [CommRing A] :=
  { E : Set (Presentation A) // E.Finite }

/-- The empty finite subset of `S(A)`, indexing the initial stage `B_∅`. -/
def emptyIndex (A : Type u) [CommRing A] : Index A :=
  ⟨∅, Set.finite_empty⟩

/-- Variables of the finite-stage algebra `B_E`, as a disjoint union of the
variable sets of the presentations in `E`. -/
abbrev StageVars (E : Index A) : Type u :=
  (p : E.1) × Fin p.1.n

/-- Rename a relation of a presentation in `E` into the disjoint-union
polynomial ring of the stage. -/
noncomputable def stageRelation (E : Index A) (x : StageVars E) :
    MvPolynomial (StageVars E) A :=
  rename (fun j : Fin x.1.1.n ↦ (⟨x.1, j⟩ : StageVars E)) (x.1.1.relations x.2)

/-- The relation ideal of the finite-stage algebra `B_E`. -/
noncomputable def stageIdeal (E : Index A) : Ideal (MvPolynomial (StageVars E) A) :=
  Ideal.span (Set.range (stageRelation E))

/-- The finite-stage algebra `B_E`, realized as a disjoint-union polynomial
quotient. For `E = {A → B₁, …, A → Bₙ}` this is the tensor product
`B₁ ⊗[A] ⋯ ⊗[A] Bₙ`. -/
abbrev stage (E : Index A) : Type u :=
  MvPolynomial (StageVars E) A ⧸ stageIdeal E

/-- Variable renaming along an inclusion `E ⊆ E'` of finite subsets of
`S(A)`. -/
def stageVarsMap {E E' : Index A} (h : E ≤ E') : StageVars E → StageVars E' :=
  fun x ↦ ⟨⟨x.1.1, h x.1.2⟩, x.2⟩

/-- Relations of `B_E` remain relations after renaming variables along
`E ⊆ E'`. -/
theorem stageMap_span_le {E E' : Index A} (h : E ≤ E') :
    stageIdeal E ≤
      (stageIdeal E').comap (rename (stageVarsMap h)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, rfl⟩
  change rename (stageVarsMap h) (stageRelation E x) ∈ stageIdeal E'
  have hrel : rename (stageVarsMap h) (stageRelation E x) =
      stageRelation E' (stageVarsMap h x) := by
    unfold stageRelation
    rw [rename_rename]
    rfl
  rw [hrel]
  exact Ideal.subset_span ⟨stageVarsMap h x, rfl⟩

/-- The canonical `A`-algebra transition `B_E → B_{E'}` along `E ⊆ E'`,
inserting `1`s in the extra tensor factors. -/
noncomputable def stageMap {E E' : Index A} (h : E ≤ E') :
    stage E →ₐ[A] stage E' :=
  Ideal.quotientMapₐ (stageIdeal E') (rename (stageVarsMap h)) (stageMap_span_le h)

/-- The empty stage has no variables. -/
instance instIsEmptyStageVarsEmpty (A : Type u) [CommRing A] :
    IsEmpty (StageVars (emptyIndex A)) :=
  ⟨fun x ↦ x.1.2⟩

/-- Comparison of the empty-stage algebra with `A`. -/
noncomputable def stageEmptyEquiv (A : Type u) [CommRing A] :
    stage (emptyIndex A) ≃+* A :=
  (Ideal.quotEquivOfEq
      ((congrArg Ideal.span (Set.range_eq_empty (stageRelation (emptyIndex A)))).trans
        Ideal.span_empty)).trans
    ((RingEquiv.quotientBot _).trans (isEmptyAlgEquiv A _).toRingEquiv)

/-- The directed system of finite-stage algebras, as a functor
`I(A) ⥤ CommRingCat`. -/
noncomputable def ringFunctor (A : Type u) [CommRing A] :
    Index A ⥤ CommRingCat.{u} where
  obj E := of (stage E)
  map f := ofHom (stageMap (leOfHom f)).toRingHom
  map_id E := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    change Ideal.Quotient.mk (stageIdeal E)
        (rename (stageVarsMap (leOfHom (𝟙 E))) p) =
      Ideal.Quotient.mk (stageIdeal E) p
    have h : stageVarsMap (leOfHom (𝟙 E)) = _root_.id := by
      funext x
      rfl
    rw [h, rename_id_apply]
  map_comp {E E' E''} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    change Ideal.Quotient.mk (stageIdeal E'')
        (rename (stageVarsMap (leOfHom (f ≫ g))) p) =
      Ideal.Quotient.mk (stageIdeal E'')
        (rename (stageVarsMap (leOfHom g)) (rename (stageVarsMap (leOfHom f)) p))
    rw [rename_rename]
    rfl

end Algebra.IndEtaleEnvelope

open Algebra.IndEtaleEnvelope

/-- The first-construction ind-étale envelope `T(A)`, as the colimit of the
finite-stage algebras `B_E` over finite subsets `E ⊆ S(A)`. -/
noncomputable def Algebra.IndEtaleEnvelope (A : Type u) [CommRing A] : Type u :=
  (colimit (ringFunctor A) : CommRingCat.{u})

namespace Algebra.IndEtaleEnvelope

variable {A : Type u} [CommRing A]

/-- The colimit ring structure on `T(A)`. -/
noncomputable instance instCommRing (A : Type u) [CommRing A] :
    CommRing (IndEtaleEnvelope A) :=
  inferInstanceAs (CommRing (colimit (ringFunctor A) : CommRingCat.{u}))

/-- The structure map `A → T(A)` through the empty-stage coprojection. -/
noncomputable def algebraMap_self (A : Type u) [CommRing A] :
    A →+* IndEtaleEnvelope A :=
  (colimit.ι (ringFunctor A) (emptyIndex A)).hom.comp
    (algebraMap A (stage (emptyIndex A)))

/-- `T(A)` is an `A`-algebra via the empty-stage coprojection. -/
noncomputable instance instAlgebra (A : Type u) [CommRing A] :
    Algebra A (IndEtaleEnvelope A) :=
  RingHom.toAlgebra (algebraMap_self A)

/-- Image of a finite subset of `S(A)` under coefficient pushforward. -/
noncomputable def indexMap {A' : Type u} [CommRing A'] (φ : A →+* A') :
    Index A ⥤ Index A' where
  obj E := ⟨Presentation.map φ '' E.1, Set.Finite.image (Presentation.map φ) E.2⟩
  map f := homOfLE (Set.image_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Variable map of a stage under coefficient pushforward, sending each
presentation in `E` to its image in `φ(E)`. -/
noncomputable def stageVarsMapAlong {A' : Type u} [CommRing A'] (φ : A →+* A')
    (E : Index A) :
    StageVars E → StageVars ((indexMap φ).obj E) :=
  fun x ↦
    ⟨⟨Presentation.map φ x.1.1, Set.mem_image_of_mem (Presentation.map φ) x.1.2⟩, x.2⟩

/-- Polynomial-level coefficient pushforward of a stage, renaming variables
along `E ↦ φ(E)`. -/
noncomputable def stagePushPoly {A' : Type u} [CommRing A'] (φ : A →+* A')
    (E : Index A) :
    MvPolynomial (StageVars E) A →+*
      MvPolynomial (StageVars ((indexMap φ).obj E)) A' :=
  (rename (stageVarsMapAlong φ E)).toRingHom.comp (MvPolynomial.map φ)

/-- Relations of `B_E` push forward into the relations of `B_{φ(E)}`. -/
theorem stageHomAlong_span_le {A' : Type u} [CommRing A'] (φ : A →+* A')
    (E : Index A) :
    stageIdeal E ≤ (stageIdeal ((indexMap φ).obj E)).comap (stagePushPoly φ E) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, rfl⟩
  change stagePushPoly φ E (stageRelation E x) ∈ stageIdeal ((indexMap φ).obj E)
  have hrel : stagePushPoly φ E (stageRelation E x) =
      stageRelation ((indexMap φ).obj E) (stageVarsMapAlong φ E x) := by
    change rename (stageVarsMapAlong φ E)
        (MvPolynomial.map φ (rename
          (fun j : Fin x.1.1.n ↦ (⟨x.1, j⟩ : StageVars E))
          (x.1.1.relations x.2))) = _
    rw [map_rename, rename_rename]
    rfl
  rw [hrel]
  exact Ideal.subset_span ⟨stageVarsMapAlong φ E x, rfl⟩

/-- The stage ring map `B_E → B_{φ(E)}` induced by coefficient pushforward. -/
noncomputable def stageHomAlong {A' : Type u} [CommRing A'] (φ : A →+* A')
    (E : Index A) : stage E →+* stage ((indexMap φ).obj E) :=
  Ideal.quotientMap (stageIdeal ((indexMap φ).obj E)) (stagePushPoly φ E)
    (stageHomAlong_span_le φ E)

/-- Natural transformation from the stage diagram of `A` to the reindexed
stage diagram of `A'`. -/
noncomputable def stageNatTrans {A' : Type u} [CommRing A'] (φ : A →+* A') :
    ringFunctor A ⟶ indexMap φ ⋙ ringFunctor A' where
  app E := ofHom (stageHomAlong φ E)
  naturality {E E'} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    change Ideal.Quotient.mk (stageIdeal ((indexMap φ).obj E'))
        (rename (stageVarsMapAlong φ E')
          (MvPolynomial.map φ (rename (stageVarsMap (leOfHom f)) p))) =
      Ideal.Quotient.mk (stageIdeal ((indexMap φ).obj E'))
        (rename (stageVarsMap (leOfHom ((indexMap φ).map f)))
          (rename (stageVarsMapAlong φ E) (MvPolynomial.map φ p)))
    rw [map_rename, rename_rename, rename_rename]
    rfl

/-- The functoriality map `T(φ) : T(A) →+* T(A')`, obtained as the colimit
comparison of the natural transformation between the finite-stage diagrams. -/
noncomputable def map {A' : Type u} [CommRing A'] (φ : A →+* A') :
    IndEtaleEnvelope A →+* IndEtaleEnvelope A' :=
  (colimitComparison (stageNatTrans φ)).hom

/-- Coprojections of `T(A)` intertwine `T(φ)` with the stage maps
`B_E → B_{φ(E)}`. -/
theorem map_ι {A' : Type u} [CommRing A'] (φ : A →+* A') (E : Index A) :
    (map φ).comp (colimit.ι (ringFunctor A) E).hom =
      (colimit.ι (ringFunctor A') ((indexMap φ).obj E)).hom.comp
        ((stageNatTrans φ).app E).hom := by
  exact congrArg CommRingCat.Hom.hom
    (colimit.ι_desc
      ((Cocone.precompose (stageNatTrans φ)).obj
        ((colimit.cocone (ringFunctor A')).whisker (indexMap φ))) E)

/-- Outer square in the category of rings: `T(φ)` commutes with the structure
maps of `T(A)` and `T(A')`. -/
theorem map_comp_algebraMap {A' : Type u} [CommRing A'] (φ : A →+* A') :
    (map φ).comp (algebraMap A (IndEtaleEnvelope A)) =
      (algebraMap A' (IndEtaleEnvelope A')).comp φ := by
  apply RingHom.ext
  intro a
  change map φ (algebraMap_self A a) = algebraMap_self A' (φ a)
  refine Eq.trans
    (RingHom.congr_fun (map_ι φ (emptyIndex A))
      (algebraMap A (stage (emptyIndex A)) a)) ?_
  change (colimit.ι (ringFunctor A') ((indexMap φ).obj (emptyIndex A))).hom
      (Ideal.Quotient.mk _ (rename _ (MvPolynomial.map φ (C a)))) =
    algebraMap_self A' (φ a)
  rw [MvPolynomial.map_C, rename_C]
  let f : emptyIndex A' ⟶ (indexMap φ).obj (emptyIndex A) :=
    homOfLE (Set.empty_subset _)
  have h := RingHom.congr_fun
    (congrArg CommRingCat.Hom.hom (colimit.w (ringFunctor A') f))
    (algebraMap A' (stage (emptyIndex A')) (φ a))
  change (colimit.ι (ringFunctor A') ((indexMap φ).obj (emptyIndex A))).hom
      (stageMap (leOfHom f) (algebraMap A' (stage (emptyIndex A')) (φ a))) =
    algebraMap_self A' (φ a) at h
  rw [AlgHom.commutes] at h
  exact h

end Algebra.IndEtaleEnvelope
