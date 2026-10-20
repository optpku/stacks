/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Tensoring a Quot-point `F_T ⟶ Q` with `L_T` yields a Quot-point of `F ⊗ L`. -/
def QuotPoint.tensor {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] : QuotPoint f (F ⊗ L) σ :=
  QuotPoint.ofEpi f (F ⊗ L) σ (Q.point.module ⊗ fiberF f L σ)
    ((Modules.PullbackTensor.tensorIso (pullback.fst f σ.hom) F L).hom ≫
      (Q.point.map ▷ fiberF f L σ))
    sorry sorry sorry sorry sorry

/-- The underlying module of a tensored Quot-point is `Q ⊗ L_T`. -/
theorem QuotPoint.tensor_module {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.module = Q.point.module ⊗ fiberF f L σ :=
  sorry

/-- The quotient map of a tensored Quot-point is the pullback-tensor comparison
`(F ⊗ L)_T ≅ F_T ⊗ L_T` followed by `map ⊗ 𝟙`. -/
theorem QuotPoint.tensor_map {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.map =
      (Modules.PullbackTensor.tensorIso (pullback.fst f σ.hom) F L).hom ≫
        (Q.point.map ▷ fiberF f L σ) :=
  sorry

/-- A tensored Quot-point is the epimorphism `(F ⊗ L)_T ⟶ Q ⊗ L_T` obtained by
tensoring `F_T ⟶ Q` with `L_T`. -/
theorem QuotPoint.tensor_spec {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.module = Q.point.module ⊗ fiberF f L σ ∧
      (Q.tensor L).point.map =
        (Modules.PullbackTensor.tensorIso (pullback.fst f σ.hom) F L).hom ≫
        (Q.point.map ▷ fiberF f L σ) :=
  sorry

/-- Reassociation identifying `F` with `(F ⊗ L) ⊗ L⁻¹` before pullback. -/
private def tensorInvReassoc (F L : X.Modules) [isInvertibleObject L] :
    F ⟶ (F ⊗ L) ⊗ isInvertibleObject.inverse L :=
  (ρ_ F).inv ≫
    (𝟙 F ⊗ₘ (isInvertibleObject.tensorInverseIso L).inv) ≫
    (α_ F L (isInvertibleObject.inverse L)).inv

/-- Tensoring a Quot-point of `F ⊗ L` with the pullback of `L⁻¹` recovers a
Quot-point of `F`. -/
@[no_expose] def QuotPoint.tensorInv {f : X ⟶ B} [FinitePresentation f] (F L : X.Modules)
    {σ : SchemeOver B} [isInvertibleObject L]
    (Q : QuotPoint f (F ⊗ L) σ) : QuotPoint f F σ :=
  let Linv := isInvertibleObject.inverse L
  QuotPoint.ofEpi f F σ (Q.point.module ⊗ fiberF f Linv σ)
    ((Modules.pullback (pullback.fst f σ.hom)).map (tensorInvReassoc F L) ≫
      (Modules.PullbackTensor.tensorIso (pullback.fst f σ.hom) (F ⊗ L) Linv).hom ≫
        (Q.point.map ▷ fiberF f Linv σ))
    sorry sorry sorry sorry sorry

/-- The underlying module of `tensorInv` is `Q` tensored with the pullback of
`L⁻¹`. -/
theorem QuotPoint.tensorInv_module {f : X ⟶ B} [FinitePresentation f]
    (F L : X.Modules) {σ : SchemeOver B} [isInvertibleObject L]
    (Q : QuotPoint f (F ⊗ L) σ) :
    (QuotPoint.tensorInv F L Q).point.module =
      Q.point.module ⊗ fiberF f (isInvertibleObject.inverse L) σ :=
  sorry

/-- Kernel identification is preserved by tensoring Quot-points with `L_T`. -/
theorem tensor_rel (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [isInvertibleObject L] (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (quotSetoid f (F ⊗ L) σ).r (Q₁.tensor L) (Q₂.tensor L) :=
  sorry

/-- Kernel identification is preserved by the inverse tensor autoequivalence on
Quot-points. -/
theorem tensorInv_rel (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [isInvertibleObject L] (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f (F ⊗ L) σ),
      (quotSetoid f (F ⊗ L) σ).r Q₁ Q₂ →
        (quotSetoid f F σ).r (QuotPoint.tensorInv F L Q₁)
          (QuotPoint.tensorInv F L Q₂) :=
  sorry

/-- The natural transformation `Quot_{F/X/B} ⟶ Quot_{F ⊗ L / X/B}` induced by
tensoring quotients with `L_T`. -/
def tensorHom (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f F ⟶ quot f (F ⊗ L) where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
        (tensor_rel f F L σ.unop))
  naturality := sorry

/-- The component of `tensorHom` at a test scheme is the setoid quotient map of
`QuotPoint.tensor`. -/
theorem tensorHom_app (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (σ : (SchemeOver B)ᵒᵖ) :
    (tensorHom f F L).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
          (tensor_rel f F L σ.unop)) :=
  sorry

/-- The inverse natural transformation `Quot_{F ⊗ L / X/B} ⟶ Quot_{F/X/B}`
induced by tensoring with the pullback of `L⁻¹`. -/
def tensorInvHom (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f (F ⊗ L) ⟶ quot f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f (F ⊗ L) σ.unop ↦
          QuotPoint.tensorInv F L Q)
        (tensorInv_rel f F L σ.unop))
  naturality := sorry

/-- The component of `tensorInvHom` at a test scheme is the setoid quotient map
of `QuotPoint.tensorInv`. -/
theorem tensorInvHom_app (f : X ⟶ B) [FinitePresentation f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (σ : (SchemeOver B)ᵒᵖ) :
    (tensorInvHom f F L).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f (F ⊗ L) σ.unop ↦
            QuotPoint.tensorInv F L Q)
          (tensorInv_rel f F L σ.unop)) :=
  sorry

/-- Tensoring quotients with an invertible module gives a natural isomorphism of Quot functors. -/
def tensorIso (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f F ≅ quot f (F ⊗ L) where
  hom := tensorHom f F L
  inv := tensorInvHom f F L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `tensorIso` is `tensorHom`. -/
theorem tensorIso_hom (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    (tensorIso f F L).hom = tensorHom f F L :=
  sorry

/-- The inverse morphism of `tensorIso` is `tensorInvHom`. -/
theorem tensorIso_inv (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] :
    (tensorIso f F L).inv = tensorInvHom f F L :=
  sorry

/-- The component of `tensorIso` at a test scheme is the setoid quotient map of
`QuotPoint.tensor`. -/
theorem tensorIso_app (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (σ : (SchemeOver B)ᵒᵖ) :
    (tensorIso f F L).hom.app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
          (tensor_rel f F L σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
