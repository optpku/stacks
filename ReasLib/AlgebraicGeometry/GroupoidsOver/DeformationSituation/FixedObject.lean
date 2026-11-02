/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation

/-!
# Deformation situations over a fixed object

Transport of coefficient rings and kernel modules along equality of objects
over affine spectra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.DeformationSituation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- A deformation situation lies over a fixed object when their underlying
objects over spectra agree. -/
def IsOver (σ : DeformationSituation X) (ξ : ObjectOverSpec X) : Prop :=
  σ.toObjectOverSpec = ξ

/-- Lying over a fixed object is equality of the underlying objects over spectra. -/
theorem isOver_iff (σ : DeformationSituation X) (ξ : ObjectOverSpec X) :
    σ.IsOver ξ ↔ σ.toObjectOverSpec = ξ :=
  Iff.rfl

/-- A deformation situation over a fixed object has the same coefficient carrier. -/
theorem carrier_eq {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : σ.carrier = ξ.carrier :=
  congrArg ObjectOverSpec.carrier hσ

/-- The kernel of a square-zero extension, as a module over the fixed coefficient ring. -/
def kernelOver {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : ModuleCat.{u} ξ.carrier :=
  @ModuleCat.of ξ.carrier inferInstance (RingHom.ker σ.toCarrier) inferInstance
    (Eq.recOn (motive := fun (η : ObjectOverSpec X) (_h : σ.toObjectOverSpec = η) ↦
        Module η.carrier (RingHom.ker σ.toCarrier))
      hσ (inferInstance : Module σ.carrier (RingHom.ker σ.toCarrier)))

/-- The identity coefficient homomorphism transported between situations over
the same object. -/
def ringHomIdOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) : σ.carrier →+* τ.carrier :=
  Eq.recOn (motive := fun (η : ObjectOverSpec X) (_ : σ.toObjectOverSpec = η) ↦
    σ.carrier →+* η.carrier) (hσ.trans hτ.symm) (RingHom.id σ.carrier)

/-- The identity arrow on the fixed object transported between two situations. -/
def objHomIdOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) : τ.obj ⟶ σ.obj :=
  eqToHom ((congrArg ObjectOverSpec.obj hτ).trans (congrArg ObjectOverSpec.obj hσ).symm)

/-- The linear map on kernels induced by a morphism fixing the coefficient ring. -/
def kernelMapOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    kernelOver hσ ⟶ kernelOver hτ := by
  rcases σ with ⟨ξσ, sourceσ, extensionσ, toSσ, compσ⟩
  rcases τ with ⟨ξτ, sourceτ, extensionτ, toSτ, compτ⟩
  dsimp only [IsOver] at hσ hτ
  cases hσ
  cases hτ
  exact f.kernelMap ≫ (ModuleCat.restrictScalarsId'App f.toRingHom hf _).hom

/-- The induced map on kernels applies the homomorphism of source rings. -/
theorem kernelMapOver_apply {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) (i : kernelOver hσ) :
    kernelMapOver hσ hτ f hf i = ⟨f.toSourceHom i.1, Hom.kernelMap_mem f i⟩ := by
  rcases σ with ⟨ξσ, sourceσ, extensionσ, toSσ, compσ⟩
  rcases τ with ⟨ξτ, sourceτ, extensionτ, toSτ, compτ⟩
  dsimp only [IsOver] at hσ hτ
  cases hσ
  cases hτ
  rfl

/-- The stored square-zero extension transported to the fixed coefficient ring. -/
def toCarrierOverMap {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : RingHom.SquareZeroExtension.Map σ.source ξ.carrier :=
  Eq.recOn (motive := fun (η : ObjectOverSpec X) (_ : σ.toObjectOverSpec = η) ↦
    RingHom.SquareZeroExtension.Map σ.source η.carrier) hσ σ.extension

/-- The homomorphism of the transported square-zero extension. -/
abbrev toCarrierOver {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) : σ.source →+* ξ.carrier :=
  (toCarrierOverMap hσ).hom

/-- The transported homomorphism applies the stored map and casts its codomain. -/
theorem toCarrierOver_apply {σ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (a' : σ.source) :
    toCarrierOver hσ a' =
      cast (congrArg ObjectOverSpec.carrier hσ) (σ.toCarrier a') := by
  cases hσ
  rfl

/-- The transported homomorphism is a square-zero extension. -/
theorem toCarrierOver_isSquareZero {σ : DeformationSituation X}
    {ξ : ObjectOverSpec X} (hσ : σ.IsOver ξ) :
    (toCarrierOver hσ).IsSquareZeroExtension :=
  (toCarrierOverMap hσ).property

private theorem sourceHomOver_laws {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    (toCarrierOver hτ).comp f.toSourceHom = toCarrierOver hσ := by
  rcases σ with ⟨ξσ, sourceσ, extensionσ, toSσ, compσ⟩
  rcases τ with ⟨ξτ, sourceτ, extensionτ, toSτ, compτ⟩
  dsimp only [IsOver] at hσ hτ
  cases hσ
  cases hτ
  simpa only [toCarrierOver, toCarrierOverMap, hf, ringHomIdOver, RingHom.id_comp] using f.commSq

/-- A morphism fixing the coefficient ring induces a morphism of transported extensions. -/
def sourceHomOver {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    AlgebraicGeometry.Deformation.Hom (toCarrierOver hσ) (toCarrierOver hτ) :=
  AlgebraicGeometry.Deformation.Hom.of f.toSourceHom (by exact sourceHomOver_laws hσ hτ f hf)

/-- The induced morphism of transported extensions has the original source map. -/
theorem sourceHomOver_hom {σ τ : DeformationSituation X} {ξ : ObjectOverSpec X}
    (hσ : σ.IsOver ξ) (hτ : τ.IsOver ξ) (f : Hom σ τ)
    (hf : f.toRingHom = ringHomIdOver hσ hτ) :
    (sourceHomOver hσ hτ f hf).hom = f.toSourceHom :=
  rfl

/-- Short exactness of transported extensions makes the fixed-object kernel maps compose to zero. -/
theorem kernelMapOver_comp_eq_zero {σ1 σ2 σ3 : DeformationSituation X}
    {ξ : ObjectOverSpec X}
    (h1 : σ1.IsOver ξ) (h2 : σ2.IsOver ξ) (h3 : σ3.IsOver ξ)
    (f21 : Hom σ2 σ1) (f32 : Hom σ3 σ2)
    (hf21 : f21.toRingHom = ringHomIdOver h2 h1)
    (hf32 : f32.toRingHom = ringHomIdOver h3 h2)
    (hses : AlgebraicGeometry.Deformation.IsShortExact
      (sourceHomOver h2 h1 f21 hf21) (sourceHomOver h3 h2 f32 hf32)) :
    kernelMapOver h3 h2 f32 hf32 ≫ kernelMapOver h2 h1 f21 hf21 = 0 := by
  rcases σ1 with ⟨ξ1, source1, extension1, toS1, comp1⟩
  rcases σ2 with ⟨ξ2, source2, extension2, toS2, comp2⟩
  rcases σ3 with ⟨ξ3, source3, extension3, toS3, comp3⟩
  dsimp only [IsOver] at h1 h2 h3
  cases h1
  cases h2
  cases h3
  exact hses.kernel_zero

end AlgebraicGeometry.GroupoidsOver.DeformationSituation
