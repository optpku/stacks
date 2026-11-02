/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Presentation
public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section

universe v w u

namespace CommAlgCat.IndEtale

namespace BaseChangePresentation

variable (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (D : IndEtale.{v} R)

/-- The scalar lift required by the endpoint-sized ind-étale predicate. -/
abbrev Base := ULift.{max w v} S

/-- The actual tensor-product target. -/
abbrev Target := S ⊗[R] D

/-- The scalar action on the tensor target induced by the lifted base. -/
instance targetAlgebra : Algebra (Base.{v} S) (Target R S D) :=
  ((algebraMap S (Target R S D)).comp ULift.ringEquiv.toRingHom).toAlgebra

/-- The small category of all presented étale factorizations into the tensor target. -/
abbrev Index := FactorizationIndex (Base.{v} S) (Target R S D)

/-- The ring diagram of these factorizations. -/
def ringDiagram : Index R S D ⥤ CommRingCat.{max w v} :=
  diagram (Base.{v} S) (Target R S D) ⋙ forget₂ (CommAlgCat (Base.{v} S)) CommRingCat

/-- Its cocone consists of the explicit target maps of the factorizations. -/
def targetCocone : Cocone (ringDiagram R S D) where
  pt := CommRingCat.of (ULift.{w} (Target R S D))
  ι :=
    { app P := CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp P.toTarget.toRingHom)
      naturality := sorry }

variable (P : RawPresentation D)

/-- The scalar action on a tensor stage induced by the lifted scalar ring. -/
@[reducible]
def stageAlgebra (i : P.Index) : Algebra (Base.{v} S) (S ⊗[R] P.stage i) :=
  ((algebraMap S (S ⊗[R] P.stage i)).comp ULift.ringEquiv.toRingHom).toAlgebra

/-- Tensoring a bundled stage of the supplied presentation, with its lifted scalar action. -/
def Stage (i : P.Index) : CommAlgCat.{max w u v} (Base.{v} S) :=
  @CommAlgCat.of (Base.{v} S) _ (S ⊗[R] P.stage i) _ (stageAlgebra R S D P i)

/-- Every tensor stage is étale over the lifted scalar ring. -/
theorem stageEtale (i : P.Index) : Algebra.Etale (Base.{v} S) (Stage R S D P i) := by
  exact @Algebra.Etale.comp (Base.{v} S) S (Stage R S D P i) _ _
    ((ULift.ringEquiv : Base.{v} S ≃+* S).toRingHom.toAlgebra) _
    (stageAlgebra R S D P i) (inferInstance : Algebra S (S ⊗[R] P.stage i))
    (@IsScalarTower.of_algebraMap_eq (Base.{v} S) S (Stage R S D P i) _ _ _
      ((ULift.ringEquiv : Base.{v} S ≃+* S).toRingHom.toAlgebra)
      (inferInstance : Algebra S (S ⊗[R] P.stage i)) (stageAlgebra R S D P i)
      (fun _ ↦ rfl))
    (RingHom.Etale.of_bijective (f := (ULift.ringEquiv : Base.{v} S ≃+* S).toRingHom)
      ULift.ringEquiv.bijective).toAlgebra
    (@Algebra.Etale.baseChange R (P.stage i) S _ _ _ _ _ (P.stageEtale i))

/-- The tensor-stage map to the tensor target, retaining its actual polynomial data. -/
def stageToTarget (i : P.Index) : Stage R S D P i →ₐ[Base.{v} S] Target R S D where
  toRingHom :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (P.stageToTarget i)).toRingHom
  commutes' := sorry

/-- A native square presentation realizes every tensor stage in the small index. -/
def stageFactorization (i : P.Index) : Factorization (Base.{v} S) (Target R S D) :=
  Factorization.ofSubmersive (@squarePresentation (Base.{v} S) (Stage R S D P i) _ _ _
      (stageEtale R S D P i)).2
    (stageToTarget R S D P i)

/-- A cocone on the small index yields a map from each original stage by the
polynomial section of its tensor-stage presentation. -/
def stageToCocone (c : Cocone (ringDiagram R S D)) (i : P.Index) :
    P.stage i →+* c.pt :=
  ((c.ι.app (stageFactorization R S D P i)).hom.comp
    (Factorization.presentationSection
      (@squarePresentation (Base.{v} S) (Stage R S D P i) _ _ _
      (stageEtale R S D P i)).2).toRingHom).comp
      (Algebra.TensorProduct.includeRight : P.stage i →ₐ[R] (S ⊗[R] P.stage i)).toRingHom

/-- Descend by the original input colimit, then use the tensor universal property.
The fixed identity factorization supplies the scalar action; filteredness is
not used to select an object or an arrow. -/
def descend (c : Cocone (ringDiagram R S D)) :
    ULift.{w} (Target R S D) →+* c.pt := by
  let P₀ := Factorization.ofId (Base.{v} S) (Target R S D)
  -- The action is determined by the fixed cocone leg; competing cocones
  -- give different actions, so a global instance would be incoherent.
  letI : Algebra S c.pt :=
    (((c.ι.app P₀).hom.comp (algebraMap (Base.{v} S) P₀.Ring)).comp
      (ULift.ringEquiv : Base.{v} S ≃+* S).symm.toRingHom).toAlgebra
  -- Restriction of this fixed cocone action determines the R-action as well;
  -- competing cocone legs make a global instance incoherent.
  letI : Algebra R c.pt :=
    ((algebraMap S c.pt).comp (algebraMap R S)).toAlgebra
  -- This tower is for the action determined by the fixed cocone leg;
  -- competing actions make a global instance incoherent.
  letI : IsScalarTower R S c.pt := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let d : D →ₐ[R] c.pt :=
    { toRingHom := (rawPresentation D).descRing
        (stageToCocone R S D (rawPresentation D) c) (by sorry)
      commutes' := sorry }
  exact (AlgHom.liftEquiv R S D c.pt d).toRingHom.comp ULift.ringEquiv.toRingHom

/-- The explicit colimit eliminator for the endpoint-sized factorization index. -/
def isColimit : IsColimit (targetCocone R S D) where
  desc c := CommRingCat.ofHom (descend R S D c)
  fac := sorry
  uniq := sorry

end BaseChangePresentation

/-- Tensor-product base change preserves ind-étaleness. -/
theorem baseChange_indEtale (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (A : IndEtale.{v} R) :
    (algebraMap S (S ⊗[R] A)).IndEtale := by
  exact RingHom.IndEtale.baseChange A.property

/-- Tensor-product base change on ind-étale algebras. -/
def baseChange (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S] :
    IndEtale.{v} R ⥤ IndEtale.{max w v} S where
  obj A :=
    { obj := .of S (S ⊗[R] A)
      property := baseChange_indEtale R S A }
  map {A B} f :=
    { hom := CommAlgCat.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom) }

/-- The underlying algebra of a base change is the tensor product. -/
theorem baseChange_obj (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (A : IndEtale.{v} R) :
    ((baseChange.{v} R S).obj A).obj = .of S (S ⊗[R] A) := rfl

/-- Reduction modulo `I` on ind-étale algebras is the canonical base-change functor along
`A → A ⧸ I`. -/
abbrev reduction {A : Type u} [CommRing A] (I : Ideal A) :
    IndEtale.{u} A ⥤ IndEtale.{u} (A ⧸ I) :=
  baseChange A (A ⧸ I)

/-- Reduction is base change along `A → A ⧸ I`. -/
theorem reduction_eq {A : Type u} [CommRing A] (I : Ideal A) :
    reduction I = baseChange A (A ⧸ I) := rfl

/-- Reduction of an ind-étale `A`-algebra `C` is identified with `C ⧸ I C`. -/
noncomputable def reductionObjQuotEquiv {A : Type u} [CommRing A] (I : Ideal A)
    (C : IndEtale.{u} A) :
    ((reduction I).obj C) ≃ₐ[A ⧸ I] (C ⧸ Ideal.map (algebraMap A C) I) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm

/-- The reduction comparison is the inverse of the tensor-quotient algebra equivalence. -/
theorem reductionObjQuotEquiv_symm {A : Type u} [CommRing A] (I : Ideal A)
    (C : IndEtale.{u} A) :
    (reductionObjQuotEquiv I C).symm = Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I :=
  (AlgEquiv.symm_symm _).symm

end CommAlgCat.IndEtale
