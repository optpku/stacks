/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.BaseChange

/-!
# Lifting ind-étale algebras along a quotient

The right adjoint `v` of reduction modulo `I` is the colimit of the small
category of relative-dimension-zero standard-étale factorizations
`A → B → Ĉ`, representing étale factorizations up to isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section

universe u

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
theorem etale (P : Factorization A T) : Algebra.Etale A P.Ring := sorry

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

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Restriction of scalars from an ind-étale `A ⧸ I`-algebra to `A`. -/
instance instAlgebra (Cbar : IndEtale.{u} (A ⧸ I)) : Algebra A Cbar :=
  RingHom.toAlgebra ((algebraMap (A ⧸ I) Cbar).comp (algebraMap A (A ⧸ I)))

/-- The scalar tower `A → A ⧸ I → Ĉ` for an ind-étale algebra over the quotient. -/
instance instIsScalarTower (Cbar : IndEtale.{u} (A ⧸ I)) : IsScalarTower A (A ⧸ I) Cbar :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The colimit of the factorization diagram in `CommAlgCat A`. -/
abbrev liftColimit (Cbar : IndEtale.{u} (A ⧸ I)) : CommAlgCat.{u} A :=
  colimit (diagram A Cbar)

/-- Unfolding lemma for the lift colimit. -/
theorem liftColimit_eq (Cbar : IndEtale.{u} (A ⧸ I)) :
    liftColimit I Cbar = colimit (diagram A Cbar) := rfl

/-- The colimit of the factorization diagram of an ind-étale algebra over a
quotient remains ind-étale over the original ring. -/
theorem lift_obj_indEtale (Cbar : IndEtale.{u} (A ⧸ I)) :
    (algebraMap A (liftColimit I Cbar)).IndEtale := sorry

/-- Postcomposition with a map of quotient algebras gives a cocone to the
factorization colimit of its codomain. -/
def liftMapCocone {Cbar Cbar' : IndEtale.{u} (A ⧸ I)} (morphism : Cbar ⟶ Cbar') :
    Cocone (diagram A Cbar) where
  pt := liftColimit I Cbar'
  ι :=
    { app := fun presentation ↦
        colimit.ι (diagram A Cbar')
          ((Factorization.postcomposeFunctor
            (AlgHom.restrictScalars A morphism.hom.hom)).obj presentation)
      naturality := sorry }

/-- The map of factorization colimits induced by a map of quotient algebras. -/
def liftMap {Cbar Cbar' : IndEtale.{u} (A ⧸ I)} (morphism : Cbar ⟶ Cbar') :
    liftColimit I Cbar ⟶ liftColimit I Cbar' :=
  colimit.desc (diagram A Cbar) (liftMapCocone I morphism)

/-- The map of factorization colimits induced by the identity is the identity. -/
theorem liftMap_id (Cbar : IndEtale.{u} (A ⧸ I)) :
    liftMap I (𝟙 Cbar) = 𝟙 (liftColimit I Cbar) := sorry

/-- The map of factorization colimits respects composition of quotient algebra maps. -/
theorem liftMap_comp {Cbar Cbar' Cbar'' : IndEtale.{u} (A ⧸ I)}
    (first : Cbar ⟶ Cbar') (second : Cbar' ⟶ Cbar'') :
    liftMap I (first ≫ second) = liftMap I first ≫ liftMap I second := sorry

/-- The right adjoint of reduction, sending an ind-étale `A ⧸ I`-algebra `Ĉ` to
the colimit of étale factorizations `A → B → Ĉ`. -/
def lift : IndEtale.{u} (A ⧸ I) ⥤ IndEtale.{u} A where
  obj Cbar :=
    { obj := liftColimit I Cbar
      property := lift_obj_indEtale I Cbar }
  map morphism := { hom := liftMap I morphism }
  map_id Cbar := by
    apply ObjectProperty.hom_ext
    exact liftMap_id I Cbar
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact liftMap_comp I first second

/-- The underlying object of `lift I` is the colimit of the factorization diagram. -/
theorem lift_obj (Cbar : IndEtale.{u} (A ⧸ I)) :
    ((lift I).obj Cbar).obj = liftColimit I Cbar := rfl

/-- The counit of the reduction ⊣ lift adjunction at `Ĉ`, as the descent of the
target maps of factorizations after tensoring with `A ⧸ I`. -/
def counitApp (Cbar : IndEtale.{u} (A ⧸ I)) :
    (reduction I).obj ((lift I).obj Cbar) ⟶ Cbar where
  hom := CommAlgCat.ofHom (AlgHom.liftEquiv A (A ⧸ I) (liftColimit I Cbar) Cbar
    (colimit.desc (diagram A Cbar) (toTargetCocone A Cbar)).hom)

/-- The counit is the tensor-hom adjunct of the colimit descent of the target maps. -/
theorem counitApp_hom (Cbar : IndEtale.{u} (A ⧸ I)) :
    (counitApp I Cbar).hom =
      CommAlgCat.ofHom
        (AlgHom.liftEquiv A (A ⧸ I) (liftColimit I Cbar) Cbar
          (colimit.desc (diagram A Cbar) (toTargetCocone A Cbar)).hom) := rfl

/-- Reduction modulo `I` is left adjoint to the colimit lift of ind-étale algebras. -/
theorem reduction_adjunction : Nonempty (reduction I ⊣ lift I) := sorry

/-- Reduction is the left adjoint of the constructed lift functor. -/
instance instIsLeftAdjoint : (reduction I).IsLeftAdjoint where
  exists_rightAdjoint := ⟨lift I, reduction_adjunction I⟩

/-- The counit comparison for every ind-étale quotient algebra is an isomorphism. -/
theorem lift_reduction_iso {A : Type u} [CommRing A]
    (I : Ideal A) (Cbar : CommAlgCat.IndEtale.{u} (A ⧸ I)) :
    IsIso (counitApp I Cbar) := sorry

attribute [instance] lift_reduction_iso

/-- Every ind-étale `A ⧸ I`-algebra is the reduction of the explicit lift
`C = v(Ĉ)`. -/
theorem exists_lift_of_quotient {Cbar : Type u} [CommRing Cbar] [Algebra (A ⧸ I) Cbar]
    (h : (algebraMap (A ⧸ I) Cbar).IndEtale) :
    Nonempty
      (((lift I).obj (of (A ⧸ I) Cbar h) ⧸
          Ideal.map (algebraMap A ((lift I).obj (of (A ⧸ I) Cbar h))) I) ≃ₐ[A ⧸ I]
        Cbar) := sorry

/-- The reduction and lift satisfy the fully faithful right-adjoint clause. -/
theorem lift_isFullyFaithfulRightAdjoint
    {A : Type u} [CommRing A] (I : Ideal A) :
    Nonempty (reduction I ⊣ lift I) ∧ Nonempty (lift I).FullyFaithful := sorry

end CommAlgCat.IndEtale
