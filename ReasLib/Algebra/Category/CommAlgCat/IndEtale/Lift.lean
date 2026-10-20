/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The underlying ring diagram of the given factorization diagram. -/
def liftRingDiagram (Cbar : IndEtale.{u} (A ⧸ I)) :
    FactorizationIndex A Cbar ⥤ CommRingCat.{u} :=
  diagram A Cbar ⋙ forget₂ (CommAlgCat A) CommRingCat

/-- The original colimit injections, with the target's scalar lift retained. -/
def liftRingCocone (Cbar : IndEtale.{u} (A ⧸ I)) : Cocone (liftRingDiagram I Cbar) where
  pt := CommRingCat.of (ULift.{u} (liftColimit I Cbar))
  ι :=
    { app P := CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (colimit.ι (diagram A Cbar) P).hom.toRingHom)
      naturality := sorry }

/-- A ring cocone has the scalar action induced by the fixed identity stage.
No object is selected from filteredness to construct this algebra cocone. -/
def liftRingDescCocone (Cbar : IndEtale.{u} (A ⧸ I))
    (c : Cocone (liftRingDiagram I Cbar)) : Cocone (diagram A Cbar) := by
  let P₀ := Factorization.ofId A Cbar
  letI : Algebra A c.pt :=
    ((c.ι.app P₀).hom.comp (algebraMap A P₀.Ring)).toAlgebra
  exact
    { pt := CommAlgCat.of A c.pt
      ι :=
        { app P := CommAlgCat.ofHom
            { toRingHom := (c.ι.app P).hom
              commutes' := sorry }
          naturality := sorry } }

/-- The explicit ring-colimit eliminator inherited from the algebra colimit. -/
def liftRingIsColimit (Cbar : IndEtale.{u} (A ⧸ I)) :
    IsColimit (liftRingCocone I Cbar) where
  desc c := CommRingCat.ofHom
    ((colimit.desc (diagram A Cbar) (liftRingDescCocone I Cbar c)).hom.toRingHom.comp
      ULift.ringEquiv.toRingHom)
  fac := sorry
  uniq := sorry

/-- The colimit of the factorization diagram of an ind-étale algebra over a
quotient remains ind-étale over the original ring. -/
theorem lift_obj_indEtale (Cbar : IndEtale.{u} (A ⧸ I)) :
    (algebraMap A (liftColimit I Cbar)).IndEtale := by
  letI := Factorization.isFiltered (A := A) (T := Cbar)
  refine ⟨FactorizationIndex A Cbar, inferInstance, inferInstance,
    liftRingDiagram I Cbar,
    { app := fun P ↦ CommRingCat.ofHom
        ((algebraMap A P.Ring).comp ULift.ringEquiv.toRingHom)
      naturality := by sorry },
    (liftRingCocone I Cbar).ι, liftRingIsColimit I Cbar, ?_⟩
  intro P
  constructor
  · exact RingHom.Etale.stableUnderComposition ULift.ringEquiv.toRingHom
      (algebraMap A P.Ring)
      (RingHom.Etale.of_bijective
        (f := (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom)
        (ULift.ringEquiv : ULift.{u} A ≃+* A).bijective)
      (RingHom.etale_algebraMap.mpr P.etale)
  · sorry

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


/-- Each étale stage mapping to `D` maps into the factorization colimit over
`Ĉ` after postcomposition with `f`. -/
def factorizationCocone (D : IndEtale.{u} A) (Cbar : IndEtale.{u} (A ⧸ I))
    (f : D →ₐ[A] Cbar) : EtaleStageCocone D (liftColimit I Cbar) where
  app B _ _ _ g :=
    let P := (squarePresentation A B).2
    (colimit.ι (diagram A Cbar) (Factorization.ofSubmersive P (f.comp g))).hom.comp
      (Factorization.presentationSection P)
  naturality := sorry

/-- The map to the lift induced by a map to its quotient target. -/
def homToLift (D : IndEtale.{u} A) (Cbar : IndEtale.{u} (A ⧸ I))
    (f : D →ₐ[A] Cbar) : D →ₐ[A] liftColimit I Cbar :=
  (factorizationCocone I D Cbar f).desc

/-- On every étale stage, the induced map is the corresponding colimit injection
composed with the presentation's explicit polynomial section. -/
theorem homToLift_comp (D : IndEtale.{u} A) (Cbar : IndEtale.{u} (A ⧸ I))
    (f : D →ₐ[A] Cbar) (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (g : B →ₐ[A] D) :
    (homToLift I D Cbar f).comp g =
      let P := (squarePresentation A B).2
      (colimit.ι (diagram A Cbar) (Factorization.ofSubmersive P (f.comp g))).hom.comp
        (Factorization.presentationSection P) :=
  (factorizationCocone I D Cbar f).desc_comp B g

/-- The unit sends each étale stage of `D` to its factorization through the
reduction of `D`. -/
def unitApp (D : IndEtale.{u} A) : D ⟶ (lift I).obj ((reduction I).obj D) where
  hom := CommAlgCat.ofHom (homToLift I D ((reduction I).obj D)
    { toRingHom :=
        (Algebra.TensorProduct.includeRight : D →ₐ[A] ((A ⧸ I) ⊗[A] D)).toRingHom
      commutes' := sorry })

/-- The reduction/lift adjunction with the explicit colimit unit and the
original tensor-quotient comparison counit. -/
def reductionLiftAdjunction : reduction I ⊣ lift I :=
  Adjunction.mkOfUnitCounit
    { unit := { app := unitApp I, naturality := sorry }
      counit := { app := counitApp I, naturality := sorry }
      left_triangle := sorry
      right_triangle := sorry }

/-- The unit of the constructed adjunction is the stagewise colimit map. -/
@[simp]
theorem reductionLiftAdjunction_unit_app (D : IndEtale.{u} A) :
    (reductionLiftAdjunction I).unit.app D = unitApp I D := rfl

/-- The counit of the constructed adjunction is the original comparison. -/
@[simp]
theorem reductionLiftAdjunction_counit_app (Cbar : IndEtale.{u} (A ⧸ I)) :
    (reductionLiftAdjunction I).counit.app Cbar = counitApp I Cbar := rfl

/-- The Hom correspondence is built from the explicit unit and counit. -/
def reductionHomEquiv (D : IndEtale.{u} A) (Cbar : IndEtale.{u} (A ⧸ I)) :
    ((reduction I).obj D ⟶ Cbar) ≃ (D ⟶ (lift I).obj Cbar) :=
  (reductionLiftAdjunction I).homEquiv D Cbar

/-- The inverse Hom correspondence reduces a map and follows it by the counit. -/
@[simp]
theorem reductionHomEquiv_symm_apply (D : IndEtale.{u} A)
    (Cbar : IndEtale.{u} (A ⧸ I)) (f : D ⟶ (lift I).obj Cbar) :
    (reductionHomEquiv I D Cbar).symm f =
      (reduction I).map f ≫ counitApp I Cbar := rfl

/-- Reduction modulo `I` is left adjoint to the colimit lift of ind-étale algebras. -/
theorem reduction_adjunction : Nonempty (reduction I ⊣ lift I) :=
  ⟨reductionLiftAdjunction I⟩

/-- Reduction is the left adjoint of the constructed lift functor. -/
instance instIsLeftAdjoint : (reduction I).IsLeftAdjoint where
  exists_rightAdjoint := ⟨lift I, reduction_adjunction I⟩


/-- Lift the finitely many coefficients of a polynomial along the quotient map.
The only choice is from the native surjectivity of the quotient map. -/
def liftPolynomial {n : ℕ} (p : MvPolynomial (Fin n) (A ⧸ I)) :
    MvPolynomial (Fin n) A :=
  p.support.sum fun d ↦
    MvPolynomial.monomial d (Ideal.Quotient.mk_surjective (p.coeff d)).choose

/-- Lifted polynomial relations reduce to the original relations. -/
theorem map_liftPolynomial {n : ℕ} (p : MvPolynomial (Fin n) (A ⧸ I)) :
    MvPolynomial.map (Ideal.Quotient.mk I) (liftPolynomial I p) = p := sorry

/-- The determinant of the lifted square Jacobian before localization. -/
def liftedJacobian {n : ℕ} (relations : Fin n → MvPolynomial (Fin n) (A ⧸ I)) :
    MvPolynomial (Fin n) A :=
  Matrix.det (jacobiMatrix n (fun i ↦ liftPolynomial I (relations i)))

/-- Lift the relations and add a variable making the lifted Jacobian invertible. -/
def liftedRelations {n : ℕ} (relations : Fin n → MvPolynomial (Fin n) (A ⧸ I)) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) A :=
  Fin.cases
    (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ (liftedJacobian I relations) - 1)
    (fun i ↦ MvPolynomial.rename Fin.succ (liftPolynomial I (relations i)))

/-- The lifted presentation maps to the original quotient algebra. Its extra
variable maps to the ring's native total inverse of the lifted Jacobian value. -/
def liftedFactorization (Cbar : IndEtale.{u} (A ⧸ I))
    {B : Type u} [CommRing B] [Algebra (A ⧸ I) B] {n : ℕ}
    (P : Algebra.SubmersivePresentation (A ⧸ I) B (Fin n) (Fin n))
    (f : B →ₐ[A ⧸ I] Cbar) : Factorization A Cbar := by
  letI : Algebra A B :=
    ((algebraMap (A ⧸ I) B).comp (algebraMap A (A ⧸ I))).toAlgebra
  exact
    { n := n + 1
      relations := liftedRelations I P.relation
      jacobian_isUnit := sorry
      toTarget := Ideal.Quotient.liftₐ _
        (MvPolynomial.aeval (Fin.cases
          (f (Ring.inverse (MvPolynomial.aeval P.val (liftedJacobian I P.relation))))
          (fun i ↦ f (P.val i)))) (by sorry) }

/-- The map from an étale quotient stage into the reduction of the factorization
colimit. Generators map to the reductions of the corresponding lifted generators. -/
def counitInverseStage (Cbar : IndEtale.{u} (A ⧸ I))
    (B : Type u) [CommRing B] [Algebra (A ⧸ I) B] [Algebra.Etale (A ⧸ I) B]
    (f : B →ₐ[A ⧸ I] Cbar) : B →ₐ[A ⧸ I] ((reduction I).obj ((lift I).obj Cbar)) := by
  let P := (squarePresentation (A ⧸ I) B).2
  let Q := liftedFactorization I Cbar P f
  exact
    { toFun b := MvPolynomial.aeval
        (fun i ↦ (1 : A ⧸ I) ⊗ₜ[A]
          (colimit.ι (diagram A Cbar) Q).hom
            (Ideal.Quotient.mk _ (MvPolynomial.X i.succ))) (P.σ b)
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry
      commutes' := sorry }

/-- The inverse comparison on the input quotient algebra's étale stages. -/
def counitInverseCocone (Cbar : IndEtale.{u} (A ⧸ I)) :
    EtaleStageCocone Cbar ((reduction I).obj ((lift I).obj Cbar)) where
  app := counitInverseStage I Cbar
  naturality := sorry

/-- The inverse of the counit, obtained by descending the lifted-generator maps
along the original ind-étale presentation of `Ĉ`. -/
def counitInverse (Cbar : IndEtale.{u} (A ⧸ I)) :
    Cbar ⟶ (reduction I).obj ((lift I).obj Cbar) where
  hom := CommAlgCat.ofHom (counitInverseCocone I Cbar).desc

/-- The counit inverse is the lifted-generator map on each étale quotient stage. -/
theorem counitInverse_comp (Cbar : IndEtale.{u} (A ⧸ I))
    (B : Type u) [CommRing B] [Algebra (A ⧸ I) B] [Algebra.Etale (A ⧸ I) B]
    (f : B →ₐ[A ⧸ I] Cbar) :
    (counitInverse I Cbar).hom.hom.comp f = counitInverseStage I Cbar B f :=
  (counitInverseCocone I Cbar).desc_comp B f

/-- The canonical reduction/lift identification, with both maps constructed. -/
def counitIso (Cbar : IndEtale.{u} (A ⧸ I)) :
    (reduction I).obj ((lift I).obj Cbar) ≅ Cbar where
  hom := counitApp I Cbar
  inv := counitInverse I Cbar
  hom_inv_id := sorry
  inv_hom_id := sorry

@[simp]
theorem counitIso_hom (Cbar : IndEtale.{u} (A ⧸ I)) :
    (counitIso I Cbar).hom = counitApp I Cbar := rfl

@[simp]
theorem counitIso_inv (Cbar : IndEtale.{u} (A ⧸ I)) :
    (counitIso I Cbar).inv = counitInverse I Cbar := rfl

/-- The counit comparison for every ind-étale quotient algebra is an isomorphism. -/
theorem lift_reduction_iso {A : Type u} [CommRing A]
    (I : Ideal A) (Cbar : CommAlgCat.IndEtale.{u} (A ⧸ I)) :
    IsIso (counitApp I Cbar) :=
  (counitIso I Cbar).isIso_hom

attribute [instance] lift_reduction_iso

/-- Every ind-étale `A ⧸ I`-algebra is the reduction of the explicit lift
`C = v(Ĉ)`. -/
theorem exists_lift_of_quotient {Cbar : Type u} [CommRing Cbar] [Algebra (A ⧸ I) Cbar]
    (h : (algebraMap (A ⧸ I) Cbar).IndEtale) :
    Nonempty
      (((lift I).obj (of (A ⧸ I) Cbar h) ⧸
          Ideal.map (algebraMap A ((lift I).obj (of (A ⧸ I) Cbar h))) I) ≃ₐ[A ⧸ I]
        Cbar) := sorry

/-- The inverse on morphisms of the fully faithful lift functor, computed by
reducing the map and conjugating by the explicit counit identifications. -/
def liftFullyFaithful : (lift I).FullyFaithful where
  preimage {Cbar Cbar'} f :=
    counitInverse I Cbar ≫ (reduction I).map f ≫ counitApp I Cbar'
  map_preimage := sorry
  preimage_map := sorry

@[simp]
theorem liftFullyFaithful_preimage {Cbar Cbar' : IndEtale.{u} (A ⧸ I)}
    (f : (lift I).obj Cbar ⟶ (lift I).obj Cbar') :
    (liftFullyFaithful I).preimage f =
      counitInverse I Cbar ≫ (reduction I).map f ≫ counitApp I Cbar' := rfl

/-- The reduction and lift satisfy the fully faithful right-adjoint clause. -/
theorem lift_isFullyFaithfulRightAdjoint
    {A : Type u} [CommRing A] (I : Ideal A) :
    Nonempty (reduction I ⊣ lift I) ∧ Nonempty (lift I).FullyFaithful :=
  ⟨⟨reductionLiftAdjunction I⟩, ⟨liftFullyFaithful I⟩⟩

end CommAlgCat.IndEtale
