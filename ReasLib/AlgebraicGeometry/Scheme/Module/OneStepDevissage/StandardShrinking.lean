/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint

/-!
# Standard shrinkings of one-step dévissages

This module records standard-open restrictions of one-step dévissages at
ambient points and at points equipped with fibre-support witnesses.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

variable {S : Scheme.{u}} {X : Over S} {ℱ : X.left.Modules}
  [h_lft : LocallyOfFiniteType X.hom] [h_qc : ℱ.IsQuasicoherent]
  [h_ft : ℱ.IsFiniteType] {x : X.left}

/-- A choice of four standard-open neighbourhoods on which a one-step dévissage
at `x` restricts to another one-step dévissage at `x`. -/
structure StandardShrinking (D : OneStepDevissageAtAmbientPoint X ℱ x) where
  /-- The chosen standard open in the base. -/
  base : S.Opens
  /-- The chosen standard open in the source. -/
  source : X.left.Opens
  /-- The chosen standard open in the auxiliary scheme. -/
  auxiliary : D.toOneStepDevissage.Z.left.Opens
  /-- The chosen standard open in the smooth model. -/
  model : D.toOneStepDevissage.Y.left.Opens
  /-- A global section defining the base standard open. -/
  baseSection : Γ(S, ⊤)
  /-- A global section defining the source standard open. -/
  sourceSection : Γ(X.left, ⊤)
  /-- A global section defining the auxiliary standard open. -/
  auxiliarySection : Γ(D.toOneStepDevissage.Z.left, ⊤)
  /-- A global section defining the model standard open. -/
  modelSection : Γ(D.toOneStepDevissage.Y.left, ⊤)
  /-- The base open is the basic open of its chosen section. -/
  base_eq_basicOpen : base = S.basicOpen baseSection
  /-- The source open is the basic open of its chosen section. -/
  source_eq_basicOpen : source = X.left.basicOpen sourceSection
  /-- The auxiliary open is the basic open of its chosen section. -/
  auxiliary_eq_basicOpen :
    auxiliary = D.toOneStepDevissage.Z.left.basicOpen auxiliarySection
  /-- The model open is the basic open of its chosen section. -/
  model_eq_basicOpen : model = D.toOneStepDevissage.Y.left.basicOpen modelSection
  /-- The image of the distinguished source point lies in the base open. -/
  basePoint_mem : X.hom x ∈ base
  /-- The distinguished source point lies in the source open. -/
  sourcePoint_mem : x ∈ source
  /-- The distinguished auxiliary point lies in the auxiliary open. -/
  auxiliaryPoint_mem : D.z ∈ auxiliary
  /-- The distinguished model point lies in the model open. -/
  modelPoint_mem : D.y ∈ model
  /-- The source open maps into the base open. -/
  source_le_base : source ≤ X.hom ⁻¹ᵁ base
  /-- The auxiliary open maps into the base open. -/
  auxiliary_le_base : auxiliary ≤ D.toOneStepDevissage.Z.hom ⁻¹ᵁ base
  /-- The model open maps into the base open. -/
  model_le_base : model ≤ D.toOneStepDevissage.Y.hom ⁻¹ᵁ base
  /-- The auxiliary open maps into the source open under `i`. -/
  auxiliary_le_source : auxiliary ≤ D.toOneStepDevissage.i.left ⁻¹ᵁ source
  /-- The auxiliary open maps into the model open under `π`. -/
  auxiliary_le_model : auxiliary ≤ D.toOneStepDevissage.π.left ⁻¹ᵁ model
  /-- The restricted closed immersion, bundled over the restricted base. -/
  restrictedI :
    Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base) ⟶
      Over.mk (X.hom.resLE base source source_le_base)
  /-- The underlying map of `restrictedI` is the canonical restriction of `i`. -/
  restrictedI_eq :
    restrictedI.left =
      D.toOneStepDevissage.i.left.resLE source auxiliary auxiliary_le_source
  /-- The restricted finite map, bundled over the restricted base. -/
  restrictedPi :
    Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base) ⟶
      Over.mk (D.toOneStepDevissage.Y.hom.resLE base model model_le_base)
  /-- The underlying map of `restrictedPi` is the canonical restriction of `π`. -/
  restrictedPi_eq :
    restrictedPi.left =
      D.toOneStepDevissage.π.left.resLE model auxiliary auxiliary_le_model
  /-- The restricted structure map of the source is locally of finite type. -/
  restrictedLocallyOfFiniteType :
    LocallyOfFiniteType (X.hom.resLE base source source_le_base)
  /-- The restriction of `ℱ` to the source open is quasicoherent. -/
  restrictedQuasicoherent :
    (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
      (Scheme.Opens.instIsOpenImmersionι source)).IsQuasicoherent
  /-- The restriction of `ℱ` to the source open is of finite type. -/
  restrictedFiniteType :
    (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
      (Scheme.Opens.instIsOpenImmersionι source)).IsFiniteType
  /-- The chosen one-step dévissage on the four restricted schemes. -/
  restricted :
    @OneStepDevissageAtAmbientPoint base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩
  /-- Its auxiliary scheme is the chosen auxiliary open over the base open. -/
  restricted_Z :
    @OneStepDevissage.Z base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted) =
      Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base)
  /-- Its smooth model is the chosen model open over the base open. -/
  restricted_Y :
    @OneStepDevissage.Y base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted) =
      Over.mk (D.toOneStepDevissage.Y.hom.resLE base model model_le_base)
  /-- Its closed immersion is the chosen canonical restriction of `i`. -/
  restricted_i :
    HEq (@OneStepDevissage.i base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted)) restrictedI
  /-- Its finite map is the chosen canonical restriction of `π`. -/
  restricted_π :
    HEq (@OneStepDevissage.π base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted)) restrictedPi
  /-- Its auxiliary module is the restriction of `D.G`. -/
  restricted_G :
    HEq (@OneStepDevissage.G base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted))
      (@Scheme.Modules.restrict auxiliary.toScheme D.toOneStepDevissage.Z.left
        D.toOneStepDevissage.G auxiliary.ι
        (Scheme.Opens.instIsOpenImmersionι auxiliary))
  /-- Its distinguished auxiliary point is the restriction of `D.z`. -/
  restricted_z :
    HEq (@OneStepDevissageAtAmbientPoint.z base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩ restricted)
      (⟨D.z, auxiliaryPoint_mem⟩ : auxiliary.toScheme)
  /-- Its distinguished model point is the restriction of `D.y`. -/
  restricted_y :
    HEq (@OneStepDevissageAtAmbientPoint.y base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩ restricted) (⟨D.y, modelPoint_mem⟩ : model.toScheme)

namespace StandardShrinking

/-- Construct a standard shrinking from four standard opens and an exactly
compatible restricted one-step dévissage. -/
def ofRestriction (D : OneStepDevissageAtAmbientPoint X ℱ x) :=
  @OneStepDevissageAtAmbientPoint.StandardShrinking.mk S X ℱ h_lft h_qc h_ft x D

/-- The restricted dévissage projection of `ofRestriction` is the supplied one. -/
theorem ofRestriction_restricted (D : OneStepDevissageAtAmbientPoint X ℱ x)
    (W : D.StandardShrinking) :
    (ofRestriction D W.base W.source W.auxiliary W.model W.baseSection
      W.sourceSection W.auxiliarySection W.modelSection W.base_eq_basicOpen
      W.source_eq_basicOpen W.auxiliary_eq_basicOpen W.model_eq_basicOpen
      W.basePoint_mem W.sourcePoint_mem W.auxiliaryPoint_mem W.modelPoint_mem
      W.source_le_base W.auxiliary_le_base W.model_le_base W.auxiliary_le_source
      W.auxiliary_le_model W.restrictedI W.restrictedI_eq W.restrictedPi
      W.restrictedPi_eq W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
      W.restrictedFiniteType W.restricted W.restricted_Z W.restricted_Y
      W.restricted_i W.restricted_π W.restricted_G W.restricted_z W.restricted_y).restricted =
        W.restricted := sorry

/-- The four chosen opens of a standard shrinking are the basic opens of their
chosen global sections. -/
theorem standardOpen_spec {D : OneStepDevissageAtAmbientPoint X ℱ x} (W : D.StandardShrinking) :
    (W.base = S.basicOpen W.baseSection ∧
      W.source = X.left.basicOpen W.sourceSection) ∧
    (W.auxiliary = D.toOneStepDevissage.Z.left.basicOpen W.auxiliarySection ∧
      W.model = D.toOneStepDevissage.Y.left.basicOpen W.modelSection) := sorry

/-- The four distinguished points belong to the corresponding chosen opens. -/
theorem point_mem_spec {D : OneStepDevissageAtAmbientPoint X ℱ x} (W : D.StandardShrinking) :
    (X.hom x ∈ W.base ∧ x ∈ W.source) ∧
      (D.z ∈ W.auxiliary ∧ D.y ∈ W.model) := sorry

/-- The restricted dévissage has exactly the restricted schemes, maps, module,
and distinguished points specified by the shrinking. -/
theorem restriction_spec {D : OneStepDevissageAtAmbientPoint X ℱ x} (W : D.StandardShrinking) :
    ((@OneStepDevissage.Z W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted) =
        Over.mk (D.toOneStepDevissage.Z.hom.resLE W.base W.auxiliary
          W.auxiliary_le_base) ∧
      @OneStepDevissage.Y W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted) =
        Over.mk (D.toOneStepDevissage.Y.hom.resLE W.base W.model W.model_le_base)) ∧
      ((HEq (@OneStepDevissage.i W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType
          ((X.hom.resLE W.base W.source W.source_le_base)
            ⟨x, W.sourcePoint_mem⟩)
          (@OneStepDevissageAtAmbientPoint.toOneStepDevissage W.base.toScheme
            (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
            (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
              (Scheme.Opens.instIsOpenImmersionι W.source))
            W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
            W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)) W.restrictedI ∧
        W.restrictedI.left = D.toOneStepDevissage.i.left.resLE W.source
          W.auxiliary W.auxiliary_le_source) ∧
      (HEq (@OneStepDevissage.π W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType
          ((X.hom.resLE W.base W.source W.source_le_base)
            ⟨x, W.sourcePoint_mem⟩)
          (@OneStepDevissageAtAmbientPoint.toOneStepDevissage W.base.toScheme
            (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
            (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
              (Scheme.Opens.instIsOpenImmersionι W.source))
            W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
            W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted))
          W.restrictedPi ∧
        W.restrictedPi.left = D.toOneStepDevissage.π.left.resLE W.model
          W.auxiliary W.auxiliary_le_model)) ∧
    ((HEq (@OneStepDevissage.G W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted))
        (@Scheme.Modules.restrict W.auxiliary.toScheme D.toOneStepDevissage.Z.left
          D.toOneStepDevissage.G W.auxiliary.ι
          (Scheme.Opens.instIsOpenImmersionι W.auxiliary)) ∧
      HEq (@OneStepDevissageAtAmbientPoint.z W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)
        (⟨D.z, W.auxiliaryPoint_mem⟩ : W.auxiliary.toScheme)) ∧
      HEq (@OneStepDevissageAtAmbientPoint.y W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)
        (⟨D.y, W.modelPoint_mem⟩ : W.model.toScheme))) := sorry

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAt

variable {S : Scheme.{u}} {X : Over S} {ℱ : X.left.Modules}
  [h_lft : LocallyOfFiniteType X.hom] [h_qc : ℱ.IsQuasicoherent]
  [h_ft : ℱ.IsFiniteType] {x : X.left}

/-- A choice of four standard-open neighbourhoods on which a one-step dévissage
at `x` restricts to another one-step dévissage at `x`. -/
structure StandardShrinking (D : OneStepDevissageAt X ℱ x) where
  /-- The chosen standard open in the base. -/
  base : S.Opens
  /-- The chosen standard open in the source. -/
  source : X.left.Opens
  /-- The chosen standard open in the auxiliary scheme. -/
  auxiliary : D.toOneStepDevissage.Z.left.Opens
  /-- The chosen standard open in the smooth model. -/
  model : D.toOneStepDevissage.Y.left.Opens
  /-- A global section defining the base standard open. -/
  baseSection : Γ(S, ⊤)
  /-- A global section defining the source standard open. -/
  sourceSection : Γ(X.left, ⊤)
  /-- A global section defining the auxiliary standard open. -/
  auxiliarySection : Γ(D.toOneStepDevissage.Z.left, ⊤)
  /-- A global section defining the model standard open. -/
  modelSection : Γ(D.toOneStepDevissage.Y.left, ⊤)
  /-- The base open is the basic open of its chosen section. -/
  base_eq_basicOpen : base = S.basicOpen baseSection
  /-- The source open is the basic open of its chosen section. -/
  source_eq_basicOpen : source = X.left.basicOpen sourceSection
  /-- The auxiliary open is the basic open of its chosen section. -/
  auxiliary_eq_basicOpen :
    auxiliary = D.toOneStepDevissage.Z.left.basicOpen auxiliarySection
  /-- The model open is the basic open of its chosen section. -/
  model_eq_basicOpen : model = D.toOneStepDevissage.Y.left.basicOpen modelSection
  /-- The image of the distinguished source point lies in the base open. -/
  basePoint_mem : X.hom x ∈ base
  /-- The distinguished source point lies in the source open. -/
  sourcePoint_mem : x ∈ source
  /-- The distinguished auxiliary point lies in the auxiliary open. -/
  auxiliaryPoint_mem : D.z ∈ auxiliary
  /-- The distinguished model point lies in the model open. -/
  modelPoint_mem : D.y ∈ model
  /-- The source open maps into the base open. -/
  source_le_base : source ≤ X.hom ⁻¹ᵁ base
  /-- The auxiliary open maps into the base open. -/
  auxiliary_le_base : auxiliary ≤ D.toOneStepDevissage.Z.hom ⁻¹ᵁ base
  /-- The model open maps into the base open. -/
  model_le_base : model ≤ D.toOneStepDevissage.Y.hom ⁻¹ᵁ base
  /-- The auxiliary open maps into the source open under `i`. -/
  auxiliary_le_source : auxiliary ≤ D.toOneStepDevissage.i.left ⁻¹ᵁ source
  /-- The auxiliary open maps into the model open under `π`. -/
  auxiliary_le_model : auxiliary ≤ D.toOneStepDevissage.π.left ⁻¹ᵁ model
  /-- The restricted closed immersion, bundled over the restricted base. -/
  restrictedI :
    Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base) ⟶
      Over.mk (X.hom.resLE base source source_le_base)
  /-- The underlying map of `restrictedI` is the canonical restriction of `i`. -/
  restrictedI_eq :
    restrictedI.left =
      D.toOneStepDevissage.i.left.resLE source auxiliary auxiliary_le_source
  /-- The restricted finite map, bundled over the restricted base. -/
  restrictedPi :
    Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base) ⟶
      Over.mk (D.toOneStepDevissage.Y.hom.resLE base model model_le_base)
  /-- The underlying map of `restrictedPi` is the canonical restriction of `π`. -/
  restrictedPi_eq :
    restrictedPi.left =
      D.toOneStepDevissage.π.left.resLE model auxiliary auxiliary_le_model
  /-- The restricted structure map of the source is locally of finite type. -/
  restrictedLocallyOfFiniteType :
    LocallyOfFiniteType (X.hom.resLE base source source_le_base)
  /-- The restriction of `ℱ` to the source open is quasicoherent. -/
  restrictedQuasicoherent :
    (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
      (Scheme.Opens.instIsOpenImmersionι source)).IsQuasicoherent
  /-- The restriction of `ℱ` to the source open is of finite type. -/
  restrictedFiniteType :
    (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
      (Scheme.Opens.instIsOpenImmersionι source)).IsFiniteType
  /-- The chosen one-step dévissage on the four restricted schemes. -/
  restricted :
    @OneStepDevissageAt base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩
  /-- Its auxiliary scheme is the chosen auxiliary open over the base open. -/
  restricted_Z :
    @OneStepDevissage.Z base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAt.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted) =
      Over.mk (D.toOneStepDevissage.Z.hom.resLE base auxiliary auxiliary_le_base)
  /-- Its smooth model is the chosen model open over the base open. -/
  restricted_Y :
    @OneStepDevissage.Y base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAt.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted) =
      Over.mk (D.toOneStepDevissage.Y.hom.resLE base model model_le_base)
  /-- Its closed immersion is the chosen canonical restriction of `i`. -/
  restricted_i :
    HEq (@OneStepDevissage.i base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAt.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted)) restrictedI
  /-- Its finite map is the chosen canonical restriction of `π`. -/
  restricted_π :
    HEq (@OneStepDevissage.π base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAt.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted)) restrictedPi
  /-- Its auxiliary module is the restriction of `D.G`. -/
  restricted_G :
    HEq (@OneStepDevissage.G base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ((X.hom.resLE base source source_le_base) ⟨x, sourcePoint_mem⟩)
      (@OneStepDevissageAt.toOneStepDevissage base.toScheme
        (Over.mk (X.hom.resLE base source source_le_base))
        (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
          (Scheme.Opens.instIsOpenImmersionι source))
        restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
        ⟨x, sourcePoint_mem⟩ restricted))
      (@Scheme.Modules.restrict auxiliary.toScheme D.toOneStepDevissage.Z.left
        D.toOneStepDevissage.G auxiliary.ι
        (Scheme.Opens.instIsOpenImmersionι auxiliary))
  /-- Its distinguished auxiliary point is the restriction of `D.z`. -/
  restricted_z :
    HEq (@OneStepDevissageAt.z base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩ restricted)
      (⟨D.z, auxiliaryPoint_mem⟩ : auxiliary.toScheme)
  /-- Its distinguished model point is the restriction of `D.y`. -/
  restricted_y :
    HEq (@OneStepDevissageAt.y base.toScheme
      (Over.mk (X.hom.resLE base source source_le_base))
      (@Scheme.Modules.restrict source.toScheme X.left ℱ source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      restrictedLocallyOfFiniteType restrictedQuasicoherent restrictedFiniteType
      ⟨x, sourcePoint_mem⟩ restricted) (⟨D.y, modelPoint_mem⟩ : model.toScheme)

namespace StandardShrinking

/-- Construct a standard shrinking from four standard opens and an exactly
compatible restricted one-step dévissage. -/
def ofRestriction (D : OneStepDevissageAt X ℱ x) :=
  @OneStepDevissageAt.StandardShrinking.mk S X ℱ h_lft h_qc h_ft x D

/-- Forget the fibre-support witnesses in a standard shrinking while retaining
all chosen opens and restriction data. -/
def toAmbientPoint (D : OneStepDevissageAt X ℱ x) (W : D.StandardShrinking) :
    (OneStepDevissageAtAmbientPoint.ofSupportPoint D).StandardShrinking where
  base := W.base
  source := W.source
  auxiliary := W.auxiliary
  model := W.model
  baseSection := W.baseSection
  sourceSection := W.sourceSection
  auxiliarySection := W.auxiliarySection
  modelSection := W.modelSection
  base_eq_basicOpen := W.base_eq_basicOpen
  source_eq_basicOpen := W.source_eq_basicOpen
  auxiliary_eq_basicOpen := W.auxiliary_eq_basicOpen
  model_eq_basicOpen := W.model_eq_basicOpen
  basePoint_mem := W.basePoint_mem
  sourcePoint_mem := W.sourcePoint_mem
  auxiliaryPoint_mem := W.auxiliaryPoint_mem
  modelPoint_mem := W.modelPoint_mem
  source_le_base := W.source_le_base
  auxiliary_le_base := W.auxiliary_le_base
  model_le_base := W.model_le_base
  auxiliary_le_source := W.auxiliary_le_source
  auxiliary_le_model := W.auxiliary_le_model
  restrictedI := W.restrictedI
  restrictedI_eq := W.restrictedI_eq
  restrictedPi := W.restrictedPi
  restrictedPi_eq := W.restrictedPi_eq
  restrictedLocallyOfFiniteType := W.restrictedLocallyOfFiniteType
  restrictedQuasicoherent := W.restrictedQuasicoherent
  restrictedFiniteType := W.restrictedFiniteType
  restricted :=
    @OneStepDevissageAtAmbientPoint.ofSupportPoint W.base.toScheme
      (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
      (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
        (Scheme.Opens.instIsOpenImmersionι W.source))
      W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent W.restrictedFiniteType
      ⟨x, W.sourcePoint_mem⟩ W.restricted
  restricted_Z := W.restricted_Z
  restricted_Y := W.restricted_Y
  restricted_i := W.restricted_i
  restricted_π := W.restricted_π
  restricted_G := W.restricted_G
  restricted_z := W.restricted_z
  restricted_y := W.restricted_y

/-- The restricted dévissage projection of `ofRestriction` is the supplied one. -/
theorem ofRestriction_restricted (D : OneStepDevissageAt X ℱ x)
    (W : D.StandardShrinking) :
    (ofRestriction D W.base W.source W.auxiliary W.model W.baseSection
      W.sourceSection W.auxiliarySection W.modelSection W.base_eq_basicOpen
      W.source_eq_basicOpen W.auxiliary_eq_basicOpen W.model_eq_basicOpen
      W.basePoint_mem W.sourcePoint_mem W.auxiliaryPoint_mem W.modelPoint_mem
      W.source_le_base W.auxiliary_le_base W.model_le_base W.auxiliary_le_source
      W.auxiliary_le_model W.restrictedI W.restrictedI_eq W.restrictedPi
      W.restrictedPi_eq W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
      W.restrictedFiniteType W.restricted W.restricted_Z W.restricted_Y
      W.restricted_i W.restricted_π W.restricted_G W.restricted_z W.restricted_y).restricted =
        W.restricted := sorry

/-- The four chosen opens of a standard shrinking are the basic opens of their
chosen global sections. -/
theorem standardOpen_spec {D : OneStepDevissageAt X ℱ x} (W : D.StandardShrinking) :
    (W.base = S.basicOpen W.baseSection ∧
      W.source = X.left.basicOpen W.sourceSection) ∧
    (W.auxiliary = D.toOneStepDevissage.Z.left.basicOpen W.auxiliarySection ∧
      W.model = D.toOneStepDevissage.Y.left.basicOpen W.modelSection) := sorry

/-- The four distinguished points belong to the corresponding chosen opens. -/
theorem point_mem_spec {D : OneStepDevissageAt X ℱ x} (W : D.StandardShrinking) :
    (X.hom x ∈ W.base ∧ x ∈ W.source) ∧
      (D.z ∈ W.auxiliary ∧ D.y ∈ W.model) := sorry

/-- The restricted dévissage has exactly the restricted schemes, maps, module,
and distinguished points specified by the shrinking. -/
theorem restriction_spec {D : OneStepDevissageAt X ℱ x} (W : D.StandardShrinking) :
    ((@OneStepDevissage.Z W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAt.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted) =
        Over.mk (D.toOneStepDevissage.Z.hom.resLE W.base W.auxiliary
          W.auxiliary_le_base) ∧
      @OneStepDevissage.Y W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAt.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted) =
        Over.mk (D.toOneStepDevissage.Y.hom.resLE W.base W.model W.model_le_base)) ∧
      ((HEq (@OneStepDevissage.i W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType
          ((X.hom.resLE W.base W.source W.source_le_base)
            ⟨x, W.sourcePoint_mem⟩)
          (@OneStepDevissageAt.toOneStepDevissage W.base.toScheme
            (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
            (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
              (Scheme.Opens.instIsOpenImmersionι W.source))
            W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
            W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)) W.restrictedI ∧
        W.restrictedI.left = D.toOneStepDevissage.i.left.resLE W.source
          W.auxiliary W.auxiliary_le_source) ∧
      (HEq (@OneStepDevissage.π W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType
          ((X.hom.resLE W.base W.source W.source_le_base)
            ⟨x, W.sourcePoint_mem⟩)
          (@OneStepDevissageAt.toOneStepDevissage W.base.toScheme
            (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
            (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
              (Scheme.Opens.instIsOpenImmersionι W.source))
            W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
            W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted))
          W.restrictedPi ∧
        W.restrictedPi.left = D.toOneStepDevissage.π.left.resLE W.model
          W.auxiliary W.auxiliary_le_model)) ∧
    ((HEq (@OneStepDevissage.G W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType
        ((X.hom.resLE W.base W.source W.source_le_base)
          ⟨x, W.sourcePoint_mem⟩)
        (@OneStepDevissageAt.toOneStepDevissage W.base.toScheme
          (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
          (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
            (Scheme.Opens.instIsOpenImmersionι W.source))
          W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
          W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted))
        (@Scheme.Modules.restrict W.auxiliary.toScheme D.toOneStepDevissage.Z.left
          D.toOneStepDevissage.G W.auxiliary.ι
          (Scheme.Opens.instIsOpenImmersionι W.auxiliary)) ∧
      HEq (@OneStepDevissageAt.z W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)
        (⟨D.z, W.auxiliaryPoint_mem⟩ : W.auxiliary.toScheme)) ∧
      HEq (@OneStepDevissageAt.y W.base.toScheme
        (Over.mk (X.hom.resLE W.base W.source W.source_le_base))
        (@Scheme.Modules.restrict W.source.toScheme X.left ℱ W.source.ι
          (Scheme.Opens.instIsOpenImmersionι W.source))
        W.restrictedLocallyOfFiniteType W.restrictedQuasicoherent
        W.restrictedFiniteType ⟨x, W.sourcePoint_mem⟩ W.restricted)
        (⟨D.y, W.modelPoint_mem⟩ : W.model.toScheme))) := sorry

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAt
