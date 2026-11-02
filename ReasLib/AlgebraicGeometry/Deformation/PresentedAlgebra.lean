/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory
public import ReasLib.RingTheory.Extension.Cotangent.Obstruction.Derived

/-! # Obstruction theory of an affine polynomial quotient -/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry GroupoidsOver
noncomputable section
universe u

namespace AlgebraicGeometry.Deformation.PresentedAlgebra

variable {Λ ι : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (J : Ideal (MvPolynomial ι Λ))

/-- The slice represented by the spectrum of a polynomial quotient over the base spectrum. -/
abbrev presentedSlice : GroupoidsOver (Spec (CommRingCat.of Λ)) :=
  GroupoidsOver.slice
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J)))))

/-- The coefficient algebra of an affine object, recovered from its structure morphism. -/
def coefficients (ξ : ObjectOverSpec (presentedSlice J)) : CommAlgCat Λ :=
  @CommAlgCat.of Λ _ ξ.carrier inferInstance (Spec.preimage ξ.toS).hom.toAlgebra

/-- The coefficient algebra of the source of a square-zero deformation. -/
private def sourceCoefficients (σ : DeformationSituation (presentedSlice J)) : CommAlgCat Λ :=
  @CommAlgCat.of Λ _ σ.source inferInstance (Spec.preimage σ.sourceToS).hom.toAlgebra

omit [IsNoetherianRing Λ] in
private theorem preimage_comp_of_spec {A B : CommRingCat.{u}}
    (a : Spec A ⟶ Spec (CommRingCat.of Λ))
    (b : Spec B ⟶ Spec (CommRingCat.of Λ)) (f : A →+* B)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = b) :
    f.comp (Spec.preimage a).hom = (Spec.preimage b).hom := by
  simpa using congrArg (fun g ↦ (Spec.preimage g).hom) h

/-- The algebra map of an affine object of the represented slice. -/
def objectAlgHom (ξ : ObjectOverSpec (presentedSlice J)) :
    (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] coefficients J ξ where
  __ := (Spec.preimage
    (eqToHom (congrArg (fun T : Over (Spec (CommRingCat.of Λ)) => T.left)
      ξ.over_obj).symm ≫ ξ.obj.hom.left)).hom
  commutes' r := by
    have h :
        (eqToHom (congrArg (fun T : Over (Spec (CommRingCat.of Λ)) => T.left)
          ξ.over_obj).symm ≫ ξ.obj.hom.left) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J))) = ξ.toS := by
      rw [← Over.eqToHom_left ξ.over_obj.symm]
      exact Over.w (eqToHom ξ.over_obj.symm ≫ ξ.obj.hom)
    have h' := congrArg (fun g ↦ (Spec.preimage g).hom) h
    erw [Spec.preimage_comp, Spec.preimage_map] at h'
    exact DFunLike.congr_fun h' r

/-- The algebra homomorphism of the stored square-zero extension. -/
private abbrev extensionAlgHom (σ : DeformationSituation (presentedSlice J)) :
    sourceCoefficients J σ →ₐ[Λ] coefficients J σ.toObjectOverSpec where
  __ := σ.toCarrier
  commutes' r :=
    DFunLike.congr_fun
      (preimage_comp_of_spec σ.sourceToS σ.toS σ.toCarrier σ.toS_comp) r

/-- The coefficient algebra homomorphism of a morphism of obstruction triples. -/
private def tripleAlgHom {ξ η : ObstructionTriple (presentedSlice J)}
    (f : ObstructionTriple.Hom ξ η) :
    coefficients J ξ.toObjectOverSpec →ₐ[Λ] coefficients J η.toObjectOverSpec where
  __ := f.toRingHom
  commutes' r :=
    DFunLike.congr_fun
      (preimage_comp_of_spec ξ.toS η.toS f.toRingHom f.toS_comp) r

omit [IsNoetherianRing Λ] in
private theorem objectAlgHom_naturality {ξ η : ObjectOverSpec (presentedSlice J)}
    (f : ObjectOverSpec.Hom ξ η)
    (a : coefficients J ξ →ₐ[Λ] coefficients J η) (ha : a.toRingHom = f.toRingHom) :
    objectAlgHom J η = a.comp (objectAlgHom J ξ) := by
  letI := f.isHomLift
  have hξ : ξ.obj.left = Over.mk ξ.toS := ξ.over_obj
  have hη : η.obj.left = Over.mk η.toS := η.over_obj
  have h := IsHomLift.fac (presentedSlice J).p
    (ObjectOverSpec.specOverMap f.toRingHom f.toS_comp) f.restriction
  change ObjectOverSpec.specOverMap f.toRingHom f.toS_comp =
    eqToHom hη.symm ≫ f.restriction.left ≫ eqToHom hξ at h
  have hbase : ObjectOverSpec.specOverMap f.toRingHom f.toS_comp ≫
      eqToHom hξ.symm ≫ ξ.obj.hom =
      eqToHom hη.symm ≫ η.obj.hom := by
    rw [h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Over.w]
  have hgeom := congrArg (fun g ↦ g.left) hbase
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (eqToHom ξ.over_obj.symm).left ≫ ξ.obj.hom.left =
      (eqToHom η.over_obj.symm).left ≫ η.obj.hom.left at hgeom
  simp only [Over.eqToHom_left] at hgeom
  have hring := congrArg (fun g ↦ (Spec.preimage g).hom) hgeom
  erw [Spec.preimage_comp, Spec.preimage_map] at hring
  rw [← ha] at hring
  ext r
  exact (DFunLike.congr_fun hring r).symm

omit [IsNoetherianRing Λ] in
private theorem objectLift_iff_sliceLift (σ : DeformationSituation (presentedSlice J)) :
    Nonempty (DeformationSituation.ObjectLift σ) ↔
      ∃ f : Over.mk σ.sourceToS ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J)))),
        σ.thickening ≫ f = eqToHom σ.over_obj.symm ≫ σ.obj.hom := by
  have hσ : σ.obj.left = Over.mk σ.toS := σ.over_obj
  constructor
  · rintro ⟨ℓ⟩
    letI := ℓ.isHomLift
    have hobj : ℓ.obj'.left = Over.mk σ.sourceToS :=
      IsHomLift.codomain_eq (presentedSlice J).p σ.thickening ℓ.hom
    refine ⟨eqToHom hobj.symm ≫ ℓ.obj'.hom, ?_⟩
    have h := IsHomLift.fac (presentedSlice J).p σ.thickening ℓ.hom
    change σ.thickening = eqToHom hσ.symm ≫ ℓ.hom.left ≫ eqToHom hobj at h
    rw [h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Over.w]
    rfl
  · rintro ⟨f, hf⟩
    have hf' : σ.thickening ≫ f = eqToHom hσ.symm ≫ σ.obj.hom := hf
    let g : σ.obj ⟶ Over.mk f := Over.homMk (eqToHom hσ ≫ σ.thickening)
      (by
        change (eqToHom hσ ≫ σ.thickening) ≫ f = σ.obj.hom
        rw [Category.assoc, hf']
        simp)
    refine ⟨⟨Over.mk f, g, ?_⟩⟩
    exact IsHomLift.of_fac' (presentedSlice J).p σ.thickening g
      σ.over_obj rfl (by
        change eqToHom hσ ≫ σ.thickening = eqToHom hσ ≫ σ.thickening ≫ 𝟙 _
        simp)

/-- Geometric lifts of an affine slice object are precisely lifts of its algebra map. -/
private theorem objectLift_iff_hasLift (σ : DeformationSituation (presentedSlice J)) :
    Nonempty (DeformationSituation.ObjectLift σ) ↔
      AlgHom.HasLift (extensionAlgHom J σ) (objectAlgHom J σ.toObjectOverSpec) := by
  rw [objectLift_iff_sliceLift]
  constructor
  · rintro ⟨f, hf⟩
    let a : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] sourceCoefficients J σ :=
      { __ := (Spec.preimage f.left).hom
        commutes' r := by
          have h := congrArg (fun g ↦ (Spec.preimage g).hom) (Over.w f)
          erw [Spec.preimage_comp, Spec.preimage_map] at h
          exact DFunLike.congr_fun h r }
    refine ⟨a, ?_⟩
    have h := congrArg (fun g ↦ (Spec.preimage g.left).hom) hf
    simp only [Over.comp_left, Over.eqToHom_left] at h
    erw [Spec.preimage_comp, Spec.preimage_map] at h
    ext r
    exact DFunLike.congr_fun h r
  · rintro ⟨a, ha⟩
    have hover : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J))) =
        σ.sourceToS := by
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom
        (a.toRingHom.comp (algebraMap Λ (MvPolynomial ι Λ ⧸ J)))) = σ.sourceToS
      erw [a.comp_algebraMap]
      exact Spec.map_preimage _
    refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) hover, ?_⟩
    apply Over.OverMorphism.ext
    have h := congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g.toRingHom)) ha
    change Spec.map (CommRingCat.ofHom ((extensionAlgHom J σ).comp a).toRingHom) =
      Spec.map (CommRingCat.ofHom (objectAlgHom J σ.toObjectOverSpec).toRingHom) at h
    erw [Spec.map_comp, Spec.map_preimage] at h
    change Spec.map (CommRingCat.ofHom σ.toCarrier) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) =
        (eqToHom σ.over_obj.symm).left ≫ σ.obj.hom.left
    rw [Over.eqToHom_left]
    exact h

omit [IsNoetherianRing Λ] in
private theorem coefficientMap_eq_zero_iff {A : Type u} [CommRing A] [Algebra Λ A]
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) {M N : ModuleCat A}
    (e : M ≃ₗ[A] N) (x : Algebra.NaiveCotangent.Obstruction.functorObj J φ M) :
    Algebra.NaiveCotangent.Obstruction.coefficientMap J φ φ (AlgHom.id Λ A)
      (by ext; rfl) e.toLinearMap x = 0 ↔ x = 0 := by
  let g := Algebra.NaiveCotangent.Obstruction.coefficientMap J φ φ (AlgHom.id Λ A)
    (by ext; rfl) e.symm.toLinearMap
  have hleft : g (Algebra.NaiveCotangent.Obstruction.coefficientMap J φ φ
      (AlgHom.id Λ A) (by ext; rfl) e.toLinearMap x) = x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    change Submodule.Quotient.mk
      (e.symm.toLinearMap.comp (e.toLinearMap.comp y)) = Submodule.Quotient.mk y
    apply congrArg Submodule.Quotient.mk
    ext z
    exact e.symm_apply_apply (y z)
  constructor
  · intro h
    rw [h] at hleft
    exact hleft.symm.trans (map_zero g)
  · intro h
    rw [h, map_zero]

/-- The cotangent Hom cokernel and polynomial-evaluation class form an obstruction theory
for the slice represented by an affine polynomial quotient. -/
def theory : GroupoidsOver.ObstructionTheory (presentedSlice J) where
  module ξ := Algebra.NaiveCotangent.Obstruction.functor
    (A := coefficients J ξ) J (objectAlgHom J ξ)
  moduleLinear ξ := Algebra.NaiveCotangent.Obstruction.functorModuleLinear
    (A := coefficients J ξ) J (objectAlgHom J ξ)
  map {ξ η} f := ConcreteCategory.ofHom
    (Algebra.NaiveCotangent.Obstruction.coefficientMap J
      (objectAlgHom J ξ.toObjectOverSpec) (objectAlgHom J η.toObjectOverSpec)
      (tripleAlgHom J f) (objectAlgHom_naturality J f.toHom (tripleAlgHom J f) rfl)
      (N := ξ.M) (N' := η.M)
      { toFun := f.toModule
        map_add' := f.toModule.hom.map_add
        map_smul' := f.toModule.hom.map_smul })
  obstruction σ :=
    Algebra.NaiveCotangent.Obstruction.coefficientMap J
      (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J σ.toObjectOverSpec)
      (AlgHom.id Λ (coefficients J σ.toObjectOverSpec)) (by ext; rfl)
      (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
        (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
      (N' := σ.kernelModule) σ.kernelModuleComparison.toLinearMap
      (Algebra.NaiveCotangent.Obstruction.obstruction
        (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec))
  map_id ξ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    rfl
  map_comp {ξ η ζ} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro y
    rfl
  map_module ξ {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_obstruction {σ τ} f := by
    let a : sourceCoefficients J σ →ₐ[Λ] sourceCoefficients J τ :=
      { __ := f.toSourceHom
        commutes' r := DFunLike.congr_fun
          (preimage_comp_of_spec σ.sourceToS τ.sourceToS f.toSourceHom
            f.sourceToS_comp) r }
    let b : coefficients J σ.toObjectOverSpec →ₐ[Λ] coefficients J τ.toObjectOverSpec :=
      tripleAlgHom J f.toTripleHom
    have hcomm : (extensionAlgHom J τ).comp a = b.comp (extensionAlgHom J σ) := by
      ext r
      exact DFunLike.congr_fun f.commSq r
    have hφ := objectAlgHom_naturality J f.toHom b rfl
    let m : σ.kernelModule →ₛₗ[f.toRingHom] τ.kernelModule :=
      { toFun := f.kernelMap
        map_add' := f.kernelMap.hom.map_add
        map_smul' := f.kernelMap.hom.map_smul }
    have h₁ := Algebra.NaiveCotangent.Obstruction.coefficientMap_comp J
      (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J σ.toObjectOverSpec)
      (objectAlgHom J τ.toObjectOverSpec)
      (AlgHom.id Λ (coefficients J σ.toObjectOverSpec)) b (by ext; rfl) hφ
      (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
        (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
      (N' := σ.kernelModule) (N'' := τ.kernelModule)
      σ.kernelModuleComparison.toLinearMap m
      (Algebra.NaiveCotangent.Obstruction.obstruction
        (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec))
    have h₂ := Algebra.NaiveCotangent.Obstruction.coefficientMap_comp J
      (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J τ.toObjectOverSpec)
      (objectAlgHom J τ.toObjectOverSpec)
      b (AlgHom.id Λ (coefficients J τ.toObjectOverSpec)) hφ (by ext; rfl)
      (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
        (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
      (N' := ModuleCat.of (coefficients J τ.toObjectOverSpec)
        (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J τ).toRingHom))
      (N'' := τ.kernelModule)
      (Algebra.NaiveCotangent.Obstruction.kernelMap
        (extensionAlgHom J σ) (extensionAlgHom J τ) a b hcomm)
      τ.kernelModuleComparison.toLinearMap
      (Algebra.NaiveCotangent.Obstruction.obstruction
        (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec))
    exact h₁.trans (h₂.symm.trans (congrArg
      (Algebra.NaiveCotangent.Obstruction.coefficientMap J
        (objectAlgHom J τ.toObjectOverSpec) (objectAlgHom J τ.toObjectOverSpec)
        (AlgHom.id Λ (coefficients J τ.toObjectOverSpec)) (by ext; rfl)
        (N := ModuleCat.of (coefficients J τ.toObjectOverSpec)
          (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J τ).toRingHom))
        (N' := τ.kernelModule) τ.kernelModuleComparison.toLinearMap)
      (Algebra.NaiveCotangent.Obstruction.map_obstruction
        (extensionAlgHom J σ) (extensionAlgHom J τ) J
        (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J τ.toObjectOverSpec)
        a b hcomm hφ)))
  lifts_iff σ := by
    exact (objectLift_iff_hasLift J σ).trans
      ((Algebra.NaiveCotangent.Obstruction.eq_zero_iff_hasLift
        (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec)).symm.trans
        (coefficientMap_eq_zero_iff J (objectAlgHom J σ.toObjectOverSpec)
          (M := ModuleCat.of (coefficients J σ.toObjectOverSpec)
            (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
          (N := σ.kernelModule)
          σ.kernelModuleComparison _).symm)

/-- The module functor of the affine obstruction theory is the cotangent Hom cokernel. -/
theorem theory_module (ξ : ObjectOverSpec (presentedSlice J)) :
    (theory J).module ξ = Algebra.NaiveCotangent.Obstruction.functor
      (A := coefficients J ξ) J (objectAlgHom J ξ) :=
  rfl

/-- The affine obstruction element is the polynomial-evaluation class transported by
the identity comparison of kernel modules. -/
theorem theory_obstruction (σ : DeformationSituation (presentedSlice J)) :
    (theory J).obstruction σ =
      Algebra.NaiveCotangent.Obstruction.coefficientMap J
        (objectAlgHom J σ.toObjectOverSpec) (objectAlgHom J σ.toObjectOverSpec)
        (AlgHom.id Λ (coefficients J σ.toObjectOverSpec)) (by ext; rfl)
        (N := ModuleCat.of (coefficients J σ.toObjectOverSpec)
          (RingHom.SquareZeroExtension.KernelModule (extensionAlgHom J σ).toRingHom))
        (N' := σ.kernelModule) σ.kernelModuleComparison.toLinearMap
        (Algebra.NaiveCotangent.Obstruction.obstruction
          (extensionAlgHom J σ) J (objectAlgHom J σ.toObjectOverSpec)) :=
  rfl

end AlgebraicGeometry.Deformation.PresentedAlgebra
