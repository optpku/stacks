/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra

/-! # Fraction-induced Serre maps on the natural projective domain -/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.GradedMap

variable {A B : Type u} [CommRing A] [CommRing B]
variable {𝒜 : ℕ → Submodule ℤ A} {ℬ : ℕ → Submodule ℤ B}
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- Denominators outside the inverse-image prime remain outside the target prime. -/
theorem partial_maps_primeCompl (ψ : 𝒜 →+*ᵍ ℬ) (x : (projMapDomain ψ).toScheme) :
    ∀ s : ((projMapMap ψ) x).asHomogeneousIdeal.toIdeal.primeCompl,
      ψ (s : A) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl := sorry

/-- The open of the ambient target on which inverse-image sections are evaluated. -/
def partialSectionOpen (ψ : 𝒜 →+*ᵍ ℬ) (U : (Proj 𝒜).Opens) : (Proj ℬ).Opens :=
  (projMapDomain ψ).ι ''ᵁ (projMapMap ψ ⁻¹ᵁ U)

/-- Apply the homogeneous-fraction map pointwise on the genuine partial domain. -/
def partialPointFamily (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : sections 𝒜 (regularShift 𝒜 n) U) :
    PointFamily ℬ (regularShift ℬ n) (partialSectionOpen ψ U) :=
  fun x ↦
    let y : (projMapDomain ψ).toScheme :=
      ⟨x.1, (projMapDomain ψ).ι_image_le _ x.2⟩
    localizedTwistMap ψ (((projMapMap ψ) y).asHomogeneousIdeal.toIdeal.primeCompl)
      x.1.asHomogeneousIdeal.toIdeal.primeCompl (partial_maps_primeCompl ψ y) n
      (s.1 ⟨projMapMap ψ y,
        ((projMapDomain ψ).mem_ι_image_iff (x := y)
          (V := projMapMap ψ ⁻¹ᵁ U)).mp x.2⟩)

/-- Fraction-induced point families are locally represented by homogeneous fractions. -/
theorem partialPointFamily_isLocallyRepresentable (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (Proj 𝒜).Opens) (s : sections 𝒜 (regularShift 𝒜 n) U) :
    IsLocallyRepresentable ℬ (regularShift ℬ n) (partialSectionOpen ψ U)
      (partialPointFamily ψ n U s) := sorry

/-- The section map on the image open sends each fraction to its image fraction. -/
def partialSectionMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op U)) :
    (twistingSheaf ℬ n).val.obj (op (partialSectionOpen ψ U)) :=
  ⟨partialPointFamily ψ n U s, partialPointFamily_isLocallyRepresentable ψ n U s⟩

/-- The section maps are additive and linear for the direct-image scalar action. -/
theorem partialDirectImageApp_laws (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (Proj 𝒜).Opens) :
    (∀ s t, partialSectionMap ψ n U (s + t) =
      partialSectionMap ψ n U s + partialSectionMap ψ n U t) ∧
    (let N := ((Scheme.Modules.pushforward (projMapMap ψ)).obj
        ((twistingSheaf ℬ n).restrict (projMapDomain ψ).ι)).val.obj (op U)
    ∀ (r : (Proj 𝒜).ringCatSheaf.obj.obj (op U)) s,
      partialSectionMap ψ n U (r • s) =
        @SMul.smul _ N N.isModule.toSMul r (partialSectionMap ψ n U s)) := sorry

/-- Linearize the actual fraction map with the direct-image module structures. -/
def partialDirectImageApp (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : ((Proj 𝒜).Opens)ᵒᵖ) :
    (twistingSheaf 𝒜 n).val.obj U ⟶
      ((Scheme.Modules.pushforward (projMapMap ψ)).obj
        ((twistingSheaf ℬ n).restrict (projMapDomain ψ).ι)).val.obj U :=
  let M := (twistingSheaf 𝒜 n).val.obj U
  let N := ((Scheme.Modules.pushforward (projMapMap ψ)).obj
    ((twistingSheaf ℬ n).restrict (projMapDomain ψ).ι)).val.obj U
  @ModuleCat.ofHom ((Proj 𝒜).ringCatSheaf.obj.obj U) _ M N
    M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := partialSectionMap ψ n U.unop
      map_add' := (partialDirectImageApp_laws ψ n U.unop).1
      map_smul' := (partialDirectImageApp_laws ψ n U.unop).2 }

/-- Fraction maps commute with restriction of sections. -/
theorem partialDirectImageHom_naturality (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    {U V : ((Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) :
    (twistingSheaf 𝒜 n).val.map i ≫
      (ModuleCat.restrictScalars ((Proj 𝒜).ringCatSheaf.obj.map i).hom).map
        (partialDirectImageApp ψ n V) =
      partialDirectImageApp ψ n U ≫
        ((Scheme.Modules.pushforward (projMapMap ψ)).obj
          ((twistingSheaf ℬ n).restrict (projMapDomain ψ).ι)).val.map i := sorry

/-- The sheaf morphism to direct image is assembled from homogeneous-fraction maps. -/
def partialDirectImageHom (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (projMapMap ψ)).obj
      ((twistingSheaf ℬ n).restrict (projMapDomain ψ).ι) where
  val :=
    { app := partialDirectImageApp ψ n
      naturality := fun {_ _} i ↦ partialDirectImageHom_naturality ψ n i }

/-- The integral Serre comparison on the natural domain is adjoint to the fraction map. -/
def partialHom (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (Scheme.Modules.pullback (projMapMap ψ)).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback (projMapDomain ψ).ι).obj (twistingSheaf ℬ n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projMapMap ψ)).homEquiv _ _).symm
      (partialDirectImageHom ψ n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (projMapDomain ψ).ι).hom.app
      (twistingSheaf ℬ n)

/-- The adjoint section map agrees with the specified pointwise fraction construction. -/
theorem partialHom_spec (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op U)) :
    ((((Scheme.Modules.pullbackPushforwardAdjunction (projMapMap ψ)).homEquiv _ _)
      (partialHom ψ n ≫
        (Scheme.Modules.restrictFunctorIsoPullback (projMapDomain ψ).ι).inv.app
          (twistingSheaf ℬ n))).val.app (op U)).hom s =
      partialSectionMap ψ n U s := sorry

/-- The fraction comparison preserves the unit and multiplication in all integral degrees. -/
theorem partialHom_isGraded (ψ : 𝒜 →+*ᵍ ℬ) (U : (Proj 𝒜).Opens) :
    partialSectionMap ψ 0 U (CanonicalAlgebra.one 𝒜 (op U)) =
      CanonicalAlgebra.one ℬ (op (partialSectionOpen ψ U)) ∧
    ∀ (n m : ℤ) (s : (twistingSheaf 𝒜 n).val.obj (op U))
      (t : (twistingSheaf 𝒜 m).val.obj (op U)),
      partialSectionMap ψ (n + m) U (CanonicalAlgebra.mulSection 𝒜 (op U) n m s t) =
        CanonicalAlgebra.mulSection ℬ (op (partialSectionOpen ψ U)) n m
          (partialSectionMap ψ n U s) (partialSectionMap ψ m U t) := sorry

end AlgebraicGeometry.Proj.AssociatedModule.GradedMap
