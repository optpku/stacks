/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Objects

/-!
# Explicit étale factorization and ind-étale presentation data

Finite square presentations give a small index of étale factorizations.
The raw presentation interface retains the input algebra's original diagram
and its actual colimit eliminator.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TensorProduct
noncomputable section
universe u v w x

namespace Algebra.Presentation

variable {A : Type u} {B : Type v} {ι : Type w} {σ : Type x}
    [CommRing A] [CommRing B] [Algebra A B]

/-- The quotient by the displayed relations is the presented algebra.
The inverse retains the presentation's designated polynomial section.
No finiteness or smoothness assumptions are needed. -/
def relationQuotientEquiv (P : Algebra.Presentation A B ι σ) :
    (MvPolynomial ι A ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[A] B :=
  (Ideal.quotientEquivAlgOfEq A P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars A)

/-- The comparison evaluates polynomial representatives at the given generators. -/
@[simp]
theorem relationQuotientEquiv_mk (P : Algebra.Presentation A B ι σ)
    (p : MvPolynomial ι A) :
    P.relationQuotientEquiv (Ideal.Quotient.mk _ p) = MvPolynomial.aeval P.val p := by
  simp [relationQuotientEquiv]

/-- The inverse comparison reduces the supplied polynomial section modulo the relations. -/
@[simp]
theorem relationQuotientEquiv_symm_apply (P : Algebra.Presentation A B ι σ) (b : B) :
    P.relationQuotientEquiv.symm b = Ideal.Quotient.mk _ (P.σ b) := by
  simp [relationQuotientEquiv]

end Algebra.Presentation

namespace CommAlgCat.IndEtale

/-- The presented ring of a relative-dimension-zero standard-étale relation family. -/
abbrev presentationRing {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) : Type u :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations)

/-- Unfolding lemma for the presented ring of a relation family. -/
theorem presentationRing_eq {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    presentationRing n relations =
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations)) := rfl

/-- The Jacobian matrix of a square relation family, with `(i, j)`-entry the
partial derivative of the `j`-th relation with respect to the `i`-th variable. -/
def jacobiMatrix {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A) :=
  fun i j ↦ MvPolynomial.pderiv i (relations j)

/-- The Jacobian matrix is the matrix of partial derivatives of the relations. -/
theorem jacobiMatrix_apply {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) (i j : Fin n) :
    jacobiMatrix n relations i j = MvPolynomial.pderiv i (relations j) := rfl

/-- The Jacobian of a square relation family, viewed in the presented ring. -/
def presentationJacobian {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    presentationRing n relations :=
  Ideal.Quotient.mk _ (Matrix.det (jacobiMatrix n relations))

/-- The Jacobian is the determinant of the Jacobian matrix, reduced to the presented ring. -/
theorem presentationJacobian_eq {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    presentationJacobian n relations =
      Ideal.Quotient.mk _ (Matrix.det (jacobiMatrix n relations)) := rfl

/-- A relative-dimension-zero standard-étale factorization `A → B → T`. -/
structure Factorization (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] where
  /-- The common number of generators and relations. -/
  n : ℕ
  /-- The square family of relations in `n` variables. -/
  relations : Fin n → MvPolynomial (Fin n) A
  /-- The Jacobian of the presentation is a unit in the presented ring. -/
  jacobian_isUnit : IsUnit (presentationJacobian n relations)
  /-- The structure map from the presented ring to the target. -/
  toTarget : presentationRing n relations →ₐ[A] T

namespace Factorization

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- The presented ring of a factorization. -/
abbrev Ring (P : Factorization A T) : Type u :=
  presentationRing P.n P.relations

/-- The presented ring of a factorization is the quotient by its relations. -/
theorem Ring_eq (P : Factorization A T) :
    P.Ring = presentationRing P.n P.relations := rfl

/-- A factorization is étale over the base. -/
theorem etale (P : Factorization A T) : Algebra.Etale A P.Ring := by
  classical
  let Q := Algebra.PreSubmersivePresentation.naive
    (v := P.relations) (fun i ↦ i) Function.injective_id
  have hmatrix : Q.jacobiMatrix = jacobiMatrix P.n P.relations := by
    ext i j
    simp [Q, jacobiMatrix]
  let Q' : Algebra.SubmersivePresentation A P.Ring (Fin P.n) (Fin P.n) :=
    { toPreSubmersivePresentation := Q
      jacobian_isUnit := by
        rw [Q.jacobian_eq_jacobiMatrix_det, hmatrix]
        exact P.jacobian_isUnit }
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    (Q'.isStandardSmoothOfRelativeDimension
      (show Q'.dimension = 0 by simp [Algebra.Presentation.dimension]))

/-- The identity factorization `A → A → T`. -/
def ofId (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] :
    Factorization A T where
  n := 0
  relations := isEmptyElim
  jacobian_isUnit := sorry
  toTarget :=
    Ideal.Quotient.liftₐ _
      (MvPolynomial.aeval (isEmptyElim : Fin 0 → T))
      (fun a ha ↦
        Eq.trans
          (congrArg (MvPolynomial.aeval (isEmptyElim : Fin 0 → T))
            (Ideal.mem_bot.mp
              (Eq.mp
                (congrArg (fun I : Ideal (MvPolynomial (Fin 0) A) ↦ a ∈ I)
                  (Eq.trans (congrArg Ideal.span (Set.range_eq_empty isEmptyElim))
                    Ideal.span_empty))
                ha)))
          (map_zero _))

/-- The identity factorization has no generators or relations. -/
theorem ofId_n (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] :
    (ofId A T).n = 0 := rfl

/-- Package a relative-dimension-zero standard-étale presentation with a map to
the target as a factorization. -/
abbrev ofRelations (n : ℕ) (relations : Fin n → MvPolynomial (Fin n) A)
    (h : IsUnit (presentationJacobian n relations))
    (toTarget : presentationRing n relations →ₐ[A] T) :
    Factorization A T where
  n := n
  relations := relations
  jacobian_isUnit := h
  toTarget := toTarget

/-- The target map of `ofRelations` is the supplied algebra homomorphism. -/
theorem ofRelations_toTarget (n : ℕ) (relations : Fin n → MvPolynomial (Fin n) A)
    (h : IsUnit (presentationJacobian n relations))
    (toTarget : presentationRing n relations →ₐ[A] T) :
    (ofRelations n relations h toTarget).toTarget = toTarget := rfl

/-- Postcomposition of the target map of a factorization. -/
def postcompose {T' : Type u} [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (P : Factorization A T) : Factorization A T' where
  n := P.n
  relations := P.relations
  jacobian_isUnit := P.jacobian_isUnit
  toTarget := f.comp P.toTarget

/-- Postcomposition acts on the target map by composition. -/
theorem postcompose_toTarget {T' : Type u} [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') (P : Factorization A T) :
    (postcompose f P).toTarget = f.comp P.toTarget := rfl

/-- A presented factorization regarded as an algebra over its target. -/
def toOver (presentation : Factorization A T) : Over (CommAlgCat.of A T) :=
  Over.mk (CommAlgCat.ofHom presentation.toTarget)

end Factorization

/-- The small category of presented étale factorizations over a target, with
morphisms induced from the over category of commutative algebras. -/
abbrev FactorizationIndex (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] :=
  InducedCategory (Over (CommAlgCat.of A T)) (Factorization.toOver (A := A) (T := T))

/-- A morphism of factorizations over a fixed target is an algebra map of
presented rings commuting with the maps to the target. -/
structure FactorizationHom {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
    (P Q : Factorization A T) where
  /-- The underlying algebra homomorphism of presented rings. -/
  hom : P.Ring →ₐ[A] Q.Ring
  /-- The two maps to the target agree. -/
  comm : Q.toTarget.comp hom = P.toTarget

namespace FactorizationHom

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- The identity morphism of a factorization. -/
def id (P : Factorization A T) : FactorizationHom P P where
  hom := AlgHom.id A P.Ring
  comm := AlgHom.comp_id P.toTarget

/-- The identity factorization morphism is the identity algebra map. -/
theorem id_hom (P : Factorization A T) :
    (id P).hom = AlgHom.id A P.Ring := rfl

/-- Composition of factorization morphisms. -/
def comp {P Q R : Factorization A T} (f : FactorizationHom P Q)
    (g : FactorizationHom Q R) : FactorizationHom P R where
  hom := g.hom.comp f.hom
  comm := by rw [← AlgHom.comp_assoc, g.comm, f.comm]

/-- Composition of factorization morphisms is composition of algebra maps. -/
theorem comp_hom {P Q R : Factorization A T} (f : FactorizationHom P Q)
    (g : FactorizationHom Q R) :
    (comp f g).hom = g.hom.comp f.hom := rfl

/-- A commuting algebra map defines a morphism of the canonical factorization index. -/
def toIndexHom {source target : FactorizationIndex A T}
    (morphism : FactorizationHom source target) : source ⟶ target :=
  InducedCategory.homMk (Over.homMk (CommAlgCat.ofHom morphism.hom)
    (congrArg CommAlgCat.ofHom morphism.comm))

/-- A morphism of the canonical factorization index determines a commuting algebra map. -/
def ofIndexHom {source target : FactorizationIndex A T} (morphism : source ⟶ target) :
    FactorizationHom source target where
  hom := morphism.hom.left.hom
  comm := congrArg CommAlgCat.Hom.hom (Over.w morphism.hom)

end FactorizationHom

/-- The canonical induced category structure on the small factorization index. -/
@[implicit_reducible]
def Factorization.category {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] :
    Category (FactorizationIndex A T) := inferInstance

/-- The small category of presented étale factorizations over a target is filtered. -/
theorem Factorization.isFiltered {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] :
    IsFiltered (FactorizationIndex A T) := sorry

/-- Postcomposition of targets as a functor on factorization categories. -/
def Factorization.postcomposeFunctor {A T T' : Type u} [CommRing A] [CommRing T]
    [CommRing T'] [Algebra A T] [Algebra A T'] (f : T →ₐ[A] T') :
    FactorizationIndex A T ⥤ FactorizationIndex A T' where
  obj := Factorization.postcompose f
  map morphism := FactorizationHom.toIndexHom
    { hom := (FactorizationHom.ofIndexHom morphism).hom
      comm := (AlgHom.comp_assoc f _ _).trans
        (congrArg (fun targetMap ↦ f.comp targetMap)
          (FactorizationHom.ofIndexHom morphism).comm) }
  map_id _ := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp _ _ := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rfl

/-- Postcomposition functor acts by `Factorization.postcompose` on objects. -/
theorem Factorization.postcomposeFunctor_obj {A T T' : Type u} [CommRing A]
    [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'] (f : T →ₐ[A] T')
    (P : Factorization A T) :
    (Factorization.postcomposeFunctor f).obj P = Factorization.postcompose f P := rfl

/-- The diagram of presented rings of factorizations over a target. -/
def diagram (A : Type u) [CommRing A] (T : Type u) [CommRing T] [Algebra A T] :
    FactorizationIndex A T ⥤ CommAlgCat.{u} A :=
  inducedFunctor (Factorization.toOver (A := A) (T := T)) ⋙
    Over.forget (CommAlgCat.of A T)

/-- The factorization diagram sends a presentation to its bundled presented ring. -/
theorem diagram_obj (A : Type u) [CommRing A] (T : Type u) [CommRing T] [Algebra A T]
    (P : Factorization A T) :
    (diagram A T).obj P = .of A P.Ring := rfl

/-- The canonical cocone from presented rings of factorizations to the target. -/
def toTargetCocone (A : Type u) [CommRing A] (T : Type u) [CommRing T] [Algebra A T] :
    Cocone (diagram A T) :=
  (Over.forgetCocone (CommAlgCat.of A T)).whisker
    (inducedFunctor (Factorization.toOver (A := A) (T := T)))

/-- The cocone point of `toTargetCocone` is the bundled target algebra. -/
theorem toTargetCocone_pt (A : Type u) [CommRing A] (T : Type u) [CommRing T] [Algebra A T] :
    (toTargetCocone A T).pt = .of A T := rfl

/-- A square submersive presentation selected from the native étale presentation
theorem. Its generators, relations and polynomial section are all retained. -/
def squarePresentation (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] :
    Σ n : ℕ, Algebra.SubmersivePresentation A B (Fin n) (Fin n) := by
  classical
  let h := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp
    (inferInstance : Algebra.Etale A B)).out
  let ι := h.choose
  let hι := h.choose_spec
  let σ := hι.choose
  let hσ := hι.choose_spec
  -- The native presentation witness supplies finiteness of its selected relation index;
  -- this scoped instance lets cardinality and reindexing use that particular index.
  letI : Finite σ := hσ.choose
  let hfin := hσ.choose_spec
  -- The same witness supplies finiteness of its selected generator index,
  -- which the cardinality and reindexing API reads through typeclass inference.
  letI : Finite ι := hfin.choose
  let hp := hfin.choose_spec
  let P := hp.choose
  -- Reindexing this presentation by `Fin` requires an enumeration of its fixed generators.
  letI := Fintype.ofFinite ι
  -- Its fixed relations likewise need an enumeration for `Fintype.equivFinOfCardEq`.
  letI := Fintype.ofFinite σ
  have hdim := hp.choose_spec
  have hle := P.card_relations_le_card_vars_of_isFinite
  have hcard : Fintype.card σ = Fintype.card ι := by
    change Nat.card ι - Nat.card σ = 0 at hdim
    change Nat.card σ ≤ Nat.card ι at hle
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdim hle
    omega
  exact ⟨Fintype.card ι,
    P.reindex (Fintype.equivFin ι).symm (Fintype.equivFinOfCardEq hcard).symm⟩

namespace Factorization

/-- The quotient presentation associated to a native square submersive presentation. -/
def ofSubmersive {A T : Type u} {B : Type v} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n))
    (f : B →ₐ[A] T) : Factorization A T where
  n := n
  relations := P.relation
  jacobian_isUnit := sorry
  toTarget := f.comp P.toPresentation.relationQuotientEquiv.toAlgHom

/-- The target map factors through the canonical relation-quotient comparison. -/
theorem ofSubmersive_toTarget {A T : Type u} {B : Type v}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) (f : B →ₐ[A] T) :
    (ofSubmersive P f).toTarget =
      f.comp P.toPresentation.relationQuotientEquiv.toAlgHom := rfl

/-- On polynomial representatives the target map is the original evaluation followed by `f`. -/
@[simp]
theorem ofSubmersive_toTarget_mk {A T : Type u} {B : Type v}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) (f : B →ₐ[A] T)
    (p : MvPolynomial (Fin n) A) :
    (ofSubmersive P f).toTarget (Ideal.Quotient.mk (Ideal.span (Set.range P.relation)) p) =
      f (MvPolynomial.aeval P.val p) := by
  change f (P.toPresentation.relationQuotientEquiv (Ideal.Quotient.mk _ p)) = _
  rw [Algebra.Presentation.relationQuotientEquiv_mk]

/-- The polynomial section of a presentation induces the inverse of its
quotient evaluation map. -/
def presentationSection {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) :
    B →ₐ[A] presentationRing n P.relation :=
  P.toPresentation.relationQuotientEquiv.symm.toAlgHom

/-- The section is the inverse of the canonical relation-quotient comparison. -/
theorem presentationSection_eq {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) :
    presentationSection P = P.toPresentation.relationQuotientEquiv.symm.toAlgHom := rfl

/-- The section retains the original polynomial representative chosen by the presentation. -/
@[simp]
theorem presentationSection_apply {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) (b : B) :
    presentationSection P b = Ideal.Quotient.mk _ (P.σ b) := by
  simp [presentationSection]

/-- Passing through the presented factorization recovers the supplied map to the target. -/
@[simp]
theorem ofSubmersive_toTarget_comp_presentationSection {A T : Type u} {B : Type v}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T] {n : ℕ}
    (P : Algebra.SubmersivePresentation A B (Fin n) (Fin n)) (f : B →ₐ[A] T) :
    (ofSubmersive P f).toTarget.comp (presentationSection P) = f := by
  ext b
  change f (P.toPresentation.relationQuotientEquiv
    (P.toPresentation.relationQuotientEquiv.symm b)) = f b
  rw [AlgEquiv.apply_symm_apply]

end Factorization

/-- A filtered diagram of étale algebras over the lifted base, with compatible
structure maps and a colimit witness identifying its colimit with the lifted target. -/
structure RawPresentation {A : Type u} [CommRing A] (D : IndEtale.{v} A) where
  /-- The bundled category indexing the presentation. -/
  Index : Cat.{max u v, max u v}
  /-- The index is filtered. -/
  filtered : IsFiltered Index
  diagram : Index ⥤ CommRingCat.{max u v}
  fromBase : (Functor.const Index).obj (CommRingCat.of (ULift.{v} A)) ⟶ diagram
  toTarget : diagram ⟶ (Functor.const Index).obj (CommRingCat.of (ULift.{u} D))
  isColimit : IsColimit (Cocone.mk _ toTarget)
  etale : ∀ i, (fromBase.app i).hom.Etale
  comm : ∀ i, fromBase.app i ≫ toTarget.app i =
    CommRingCat.ofHom (algebraMap A D).ulift


/-- The filtered étale diagram, structure maps, and colimit witness supplied by
an ind-étale algebra. -/
def rawPresentation {A : Type u} [CommRing A] (D : IndEtale.{v} A) :
    RawPresentation D := by
  let h := D.property
  let J := h.choose
  let hJ := h.choose_spec
  -- The supplied ind-étale witness fixes the category structure on its selected index;
  -- the following functors and bundled category must use precisely this structure.
  letI := hJ.choose
  let hcat := hJ.choose_spec
  let hfiltered := hcat.choose_spec
  let F := hfiltered.choose
  let hF := hfiltered.choose_spec
  let t := hF.choose
  let ht := hF.choose_spec
  let s := ht.choose
  let hs := ht.choose_spec
  let hc := hs.choose
  let hst := hs.choose_spec
  exact ⟨Cat.of J, hcat.choose, F, t, s, hc, fun i ↦ (hst i).1, fun i ↦ (hst i).2⟩

namespace RawPresentation

variable {A : Type u} [CommRing A] {D : IndEtale.{v} A} (P : RawPresentation D)

/-- A stage of the presentation, bundled with its scalar action from the lifted base. -/
def stage (i : P.Index) : CommAlgCat.{max u v} A :=
  @CommAlgCat.of A _ (P.diagram.obj i) _
    (((P.fromBase.app i).hom.comp ULift.ringEquiv.symm.toRingHom).toAlgebra)

/-- The scalar action on a bundled presentation stage. -/
@[reducible]
def stageAlgebra (i : P.Index) : Algebra A (P.stage i) := inferInstance

/-- Each bundled stage is étale over the original base. -/
theorem stageEtale (i : P.Index) : Algebra.Etale A (P.stage i) := by
  exact @Algebra.Etale.comp A (ULift.{v} A) (P.stage i) _ _
    (ULift.ringEquiv.symm.toRingHom.toAlgebra) _ (P.stageAlgebra i)
    ((P.fromBase.app i).hom.toAlgebra)
    (@IsScalarTower.of_algebraMap_eq A (ULift.{v} A) (P.stage i) _ _ _
      (ULift.ringEquiv.symm.toRingHom.toAlgebra) ((P.fromBase.app i).hom.toAlgebra)
      (P.stageAlgebra i) (fun _ ↦ rfl))
    (RingHom.Etale.of_bijective (f := (ULift.ringEquiv : ULift.{v} A ≃+* A).symm.toRingHom)
      ULift.ringEquiv.symm.bijective).toAlgebra (P.etale i).toAlgebra

/-- The stage map to the input algebra, with the scalar lift removed. -/
def stageToTarget (i : P.Index) : P.stage i →ₐ[A] D where
  toRingHom := ULift.ringEquiv.toRingHom.comp (P.toTarget.app i).hom
  commutes' := sorry

/-- Descend a compatible family of stage maps to a ring in any universe.
The range of the polynomial evaluation is small enough for the original
colimit eliminator; its inclusion then returns the map to the given target. -/
def descRing {T : Type w} [CommRing T]
    (maps : ∀ i, P.stage i →+* T)
    (naturality : ∀ {i j} (f : i ⟶ j),
      (maps j).comp (P.diagram.map f).hom = maps i) : D →+* T := by
  let evaluation : MvPolynomial (Σ i : P.Index, P.stage i) ℤ →+* T :=
    MvPolynomial.eval₂Hom (Int.castRingHom T) (fun x ↦ maps x.1 x.2)
  -- The supplied colimit eliminates into rings in its own universe. Shrinking the
  -- range of this fixed evaluation gives such a ring; `Shrink` requires its scoped smallness.
  letI : Small.{max u v} evaluation.range :=
    small_of_surjective evaluation.rangeRestrict_surjective
  let c : Cocone P.diagram :=
    { pt := CommRingCat.of (Shrink.{max u v} evaluation.range)
      ι :=
        { app i := CommRingCat.ofHom
            { toFun x := (Shrink.ringEquiv evaluation.range).symm
                ⟨maps i x, ⟨MvPolynomial.X ⟨i, x⟩, by simp [evaluation]⟩⟩
              map_zero' := sorry
              map_one' := sorry
              map_add' := sorry
              map_mul' := sorry }
          naturality := sorry } }
  exact evaluation.range.subtype.comp
    ((Shrink.ringEquiv evaluation.range).toRingHom.comp
      ((P.isColimit.desc c).hom.comp ULift.ringEquiv.symm.toRingHom))

/-- The universe-independent descent map recovers its prescribed stage maps. -/
theorem descRing_comp {T : Type w} [CommRing T]
    (maps : ∀ i, P.stage i →+* T)
    (naturality : ∀ {i j} (f : i ⟶ j),
      (maps j).comp (P.diagram.map f).hom = maps i) (i : P.Index) :
    (P.descRing maps naturality).comp (P.stageToTarget i).toRingHom = maps i := sorry

end RawPresentation

/-- A compatible family of algebra maps on all étale stages mapping to `D`.
This is used internally to descend the explicit factorization maps. -/
structure EtaleStageCocone {A : Type u} [CommRing A] (D : IndEtale.{u} A)
    (T : Type u) [CommRing T] [Algebra A T] where
  app : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B],
    (B →ₐ[A] D) → B →ₐ[A] T
  naturality : ∀ (B B' : Type u) [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] [Algebra.Etale A B] [Algebra.Etale A B']
    (g : B →ₐ[A] B') (f : B' →ₐ[A] D),
    (app B' f).comp g = app B (f.comp g)

namespace EtaleStageCocone

variable {A : Type u} [CommRing A] {D : IndEtale.{u} A}
    {T : Type u} [CommRing T] [Algebra A T] (c : EtaleStageCocone D T)

/-- Restrict the compatible stage maps to the input algebra's original diagram. -/
def rawCocone : Cocone (rawPresentation D).diagram where
  pt := CommRingCat.of T
  ι :=
    { app i := CommRingCat.ofHom
        (@EtaleStageCocone.app _ _ _ _ _ _ c ((rawPresentation D).stage i)
          _ _ ((rawPresentation D).stageEtale i)
          ((rawPresentation D).stageToTarget i)).toRingHom
      naturality := sorry }

/-- Descent along the original, supplied ind-étale colimit witness. -/
def desc : D →ₐ[A] T where
  toRingHom := ((rawPresentation D).isColimit.desc c.rawCocone).hom.comp
    ULift.ringEquiv.symm.toRingHom
  commutes' := sorry

/-- The descended map restricts to the designated map on each étale stage. -/
theorem desc_comp (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (f : B →ₐ[A] D) :
    c.desc.comp f = c.app B f := sorry

end EtaleStageCocone


end CommAlgCat.IndEtale
