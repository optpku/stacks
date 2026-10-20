/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Local

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- The section-ring map on a compatible pair of affine opens is finite-type
quasi-finite. -/
theorem affineQuasiFinite (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    RingHom.FiniteType.QuasiFinite (f.appLE U V hVU).hom := sorry

/-- Pulling back a principal affine open along a compatible affine section map gives the
corresponding principal affine open in the source. -/
theorem affineBasicOpen_le_preimage (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    Y.affineBasicOpen ((f.appLE U V hVU).hom a) ≤
      f ⁻¹ᵁ X.affineBasicOpen a := sorry

/-- A target principal open remains inside the inverse image of the same affine base open. -/
theorem affineBasicOpen_target_le (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U) (b : Γ(Y, V)) :
    Y.affineBasicOpen b ≤ f ⁻¹ᵁ U := sorry

/-- The semilinear restriction map on module sections between nested affine opens. -/
noncomputable def restrictSections (M : Y.Modules) (V V' : Y.affineOpens)
    (hV : V' ≤ V) :
    Γ(M, V) →ₛₗ[
      (Y.presheaf.map
        (homOfLE (X := Y.Opens) hV).op).hom] Γ(M, V') :=
  M.val.restrictₛₗ (homOfLE (X := Y.Opens) hV).op

/-- The linear-map view of restriction after restricting scalars to the larger affine
section ring. -/
def restrictSectionsLinear (M : Y.Modules) (V V' : Y.affineOpens)
    (hV : V' ≤ V) :
    Γ(M, V) →ₗ[Γ(Y, V)]
      (ModuleCat.restrictScalars
        (Y.presheaf.map
          (homOfLE (X := Y.Opens) hV).op).hom).obj
        ((RingedSpace.moduleSectionsEvaluationFunctor
          Y.toRingedSpace V').obj M) :=
  (M.val.map (homOfLE (X := Y.Opens) hV).op).hom

/-- The section module on an affine principal open, regarded as a module over the ring of
sections on the ambient affine open. -/
abbrev principalSections (M : Y.Modules) (V : Y.affineOpens) (b : Γ(Y, V)) :
    ModuleCat Γ(Y, V) :=
  (ModuleCat.restrictScalars
    (Y.presheaf.map
      (homOfLE (X := Y.Opens) (Y.affineBasicOpen_le b)).op).hom).obj
    ((RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace
      (Y.affineBasicOpen b)).obj M)

/-- The module of a localized presentation, regarded over the original target ring. -/
abbrev _root_.Algebra.RelativeDualizingModule.Presentation.awayModuleRestricted
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Algebra.RelativeDualizingModule.Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) : ModuleCat B :=
  (ModuleCat.restrictScalars
    (algebraMap B (Localization.Away (phi.hom a)))).obj
    ((P.away hA a).module inferInstance inferInstance
      (P.away_quasiFinite hA h a))

/-- The module of a target-localized presentation, regarded over the original target ring. -/
abbrev _root_.Algebra.RelativeDualizingModule.Presentation.awayTargetModuleRestricted
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Algebra.RelativeDualizingModule.Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) : ModuleCat B :=
  (ModuleCat.restrictScalars (algebraMap B (Localization.Away b))).obj
    (P.awayTargetModule hA hB h b)

/-- The canonical principal-localization map of a presentation, viewed as a linear map over
the original target ring. -/
noncomputable def _root_.Algebra.RelativeDualizingModule.Presentation.awayRestrictionLinear
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Algebra.RelativeDualizingModule.Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A) :
    P.module hA hB h ⟶ P.awayModuleRestricted hA hB h a :=
  ModuleCat.ofHom
    (X := P.module hA hB h) (Y := P.awayModuleRestricted hA hB h a)
    { toFun := P.awayRestriction hA hB h a
      map_add' := (P.awayRestriction hA hB h a).map_add
      map_smul' := fun r x ↦
        (P.awayRestriction hA hB h a).map_smulₛₗ r x }

/-- The canonical target-principal localization map, viewed as a linear map over the
original target ring. -/
noncomputable def _root_.Algebra.RelativeDualizingModule.Presentation.awayTargetRestrictionLinear
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Algebra.RelativeDualizingModule.Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (b : B) :
    P.module hA hB h ⟶ P.awayTargetModuleRestricted hA hB h b :=
  ModuleCat.ofHom
    (X := P.module hA hB h) (Y := P.awayTargetModuleRestricted hA hB h b)
    { toFun := P.awayTargetRestriction hA hB h b
      map_add' := (P.awayTargetRestriction hA hB h b).map_add
      map_smul' := fun r x ↦
        (P.awayTargetRestriction hA hB h b).map_smulₛₗ r x }

/-- The linear principal-localization map is identified by `awayModuleIso` with the usual
map into the localized module. -/
theorem _root_.Algebra.RelativeDualizingModule.Presentation.awayRestrictionLinear_awayModuleIso
    {A B : CommRingCat.{u}} {phi : A ⟶ B}
    (P : Algebra.RelativeDualizingModule.Presentation phi)
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B)
    (h : RingHom.FiniteType.QuasiFinite phi.hom) (a : A)
    (x : P.module hA hB h) :
    (P.awayModuleIso hA hB h a).hom
        (P.awayRestrictionLinear hA hB h a x) =
      LocalizedModule.mkLinearMap (Submonoid.powers (phi.hom a))
        (P.module hA hB h) x := sorry

/-- A module over the smaller affine section ring, restricted to the larger affine section
ring along the actual scheme restriction map. -/
abbrev restrictedAffineModule (V V' : Y.affineOpens) (hV : V' ≤ V)
    (M : ModuleCat Γ(Y, V')) : ModuleCat Γ(Y, V) :=
  (ModuleCat.restrictScalars
    (Y.presheaf.map (homOfLE (X := Y.Opens) hV).op).hom).obj M

/-- A relative dualizing sheaf for `f` is a coherent module with explicit finite/open models
whose prescribed comparison maps agree with actual restriction on every nested affine pair. -/
structure RelativeDualizingSheaf where
  /-- The coherent module sheaf on the source. -/
  module : RingedSpace.Coh Y.toRingedSpace
  /-- A finite/open presentation on every compatible pair of affine opens. -/
  presentation : ∀ (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U),
    Algebra.RelativeDualizingModule.Presentation (f.appLE U V hVU)
  /-- The canonical affine identification with a chosen finite/open ring presentation. -/
  sectionIso : ∀ (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U),
    (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).obj module.obj ≅
      (presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU)
  /-- The canonical localization/refinement comparison for every nested compatible affine
  pair. -/
  restrictionComparison : ∀ (U U' : X.affineOpens) (hU : U' ≤ U)
      (V V' : Y.affineOpens) (hV : V' ≤ V)
      (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U'),
    (presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) →ₛₗ[
          (Y.presheaf.map (homOfLE (X := Y.Opens) hV).op).hom]
      (presentation U' V' hVU').module
        (IsLocallyNoetherian.component_noetherian U')
        (IsLocallyNoetherian.component_noetherian V')
        (affineQuasiFinite f U' V' hVU')
  /-- The prescribed comparison is exactly actual sheaf restriction transported through the
  two stored affine identifications. -/
  restriction_naturality : ∀ (U U' : X.affineOpens) (hU : U' ≤ U)
      (V V' : Y.affineOpens) (hV : V' ≤ V)
      (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U')
      (s : (RingedSpace.moduleSectionsEvaluationFunctor
        Y.toRingedSpace V).obj module.obj),
    restrictionComparison U U' hU V V' hV hVU hVU'
        ((sectionIso U V hVU).hom s) =
      (sectionIso U' V' hVU').hom
        (restrictSections module.obj V V' hV s)
  /-- The prescribed comparison for an identity inclusion is the identity map. -/
  restriction_id : ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U)
      (x : (presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU)),
    restrictionComparison U U le_rfl V V le_rfl hVU hVU x = x
  /-- Prescribed comparisons compose along nested compatible affine pairs. -/
  restriction_comp : ∀ (U₀ U₁ U₂ : X.affineOpens)
      (hU₀₁ : U₁ ≤ U₀) (hU₁₂ : U₂ ≤ U₁) (hU₀₂ : U₂ ≤ U₀)
      (V₀ V₁ V₂ : Y.affineOpens) (hV₀₁ : V₁ ≤ V₀)
      (hV₁₂ : V₂ ≤ V₁) (hV₀₂ : V₂ ≤ V₀)
      (hV₀U₀ : V₀ ≤ f ⁻¹ᵁ U₀) (hV₁U₁ : V₁ ≤ f ⁻¹ᵁ U₁)
      (hV₂U₂ : V₂ ≤ f ⁻¹ᵁ U₂)
      (x : (presentation U₀ V₀ hV₀U₀).module
        (IsLocallyNoetherian.component_noetherian U₀)
        (IsLocallyNoetherian.component_noetherian V₀)
        (affineQuasiFinite f U₀ V₀ hV₀U₀)),
    restrictionComparison U₁ U₂ hU₁₂ V₁ V₂ hV₁₂ hV₁U₁ hV₂U₂
        (restrictionComparison U₀ U₁ hU₀₁ V₀ V₁ hV₀₁ hV₀U₀ hV₁U₁ x) =
      restrictionComparison U₀ U₂ hU₀₂ V₀ V₂ hV₀₂ hV₀U₀ hV₂U₂ x
  /-- The actual smaller affine model on a pulled-back base principal open is canonically
  identified with the simultaneous localization of the larger model. -/
  basePrincipalComparison : ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)),
    restrictedAffineModule V
        (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
        (Y.affineBasicOpen_le ((f.appLE U V hVU).hom a))
        ((presentation (X.affineBasicOpen a)
          (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
          (affineBasicOpen_le_preimage f U V hVU a)).module
            (IsLocallyNoetherian.component_noetherian (X.affineBasicOpen a))
            (IsLocallyNoetherian.component_noetherian
              (Y.affineBasicOpen ((f.appLE U V hVU).hom a)))
            (affineQuasiFinite f (X.affineBasicOpen a)
              (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
              (affineBasicOpen_le_preimage f U V hVU a))) ≅
      (presentation U V hVU).awayModuleRestricted
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) a
  /-- On pulled-back base principal opens, the prescribed transition is the canonical map
  induced by `Presentation.awayModuleIso`. -/
  basePrincipal_transition : ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U))
      (x : (presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU)),
    (basePrincipalComparison U V hVU a).hom
        (restrictionComparison U (X.affineBasicOpen a)
          (X.affineBasicOpen_le a) V
          (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
          (Y.affineBasicOpen_le ((f.appLE U V hVU).hom a)) hVU
          (affineBasicOpen_le_preimage f U V hVU a) x) =
      (presentation U V hVU).awayRestrictionLinear
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) a x
  /-- The actual smaller affine model on a target principal open is canonically identified
  with the target localization governed by `RelativeDualizingModule.awayTargetIso`. -/
  targetPrincipalComparison : ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U) (b : Γ(Y, V)),
    restrictedAffineModule V (Y.affineBasicOpen b) (Y.affineBasicOpen_le b)
        ((presentation U (Y.affineBasicOpen b)
          (affineBasicOpen_target_le f U V hVU b)).module
            (IsLocallyNoetherian.component_noetherian U)
            (IsLocallyNoetherian.component_noetherian (Y.affineBasicOpen b))
            (affineQuasiFinite f U (Y.affineBasicOpen b)
              (affineBasicOpen_target_le f U V hVU b))) ≅
      (presentation U V hVU).awayTargetModuleRestricted
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) b
  /-- On target principal opens, the prescribed transition is the canonical restriction map
  obtained from `RelativeDualizingModule.awayTargetIso`. -/
  targetPrincipal_transition : ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U) (b : Γ(Y, V))
      (x : (presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU)),
    (targetPrincipalComparison U V hVU b).hom
        (restrictionComparison U U le_rfl V (Y.affineBasicOpen b)
          (Y.affineBasicOpen_le b) hVU
          (affineBasicOpen_target_le f U V hVU b) x) =
      (presentation U V hVU).awayTargetRestrictionLinear
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) b x

namespace RelativeDualizingSheaf

/-- Construct a relative dualizing sheaf from its coherent module, affine models, prescribed
restriction comparisons, and their localization and cocycle laws. -/
def of := @RelativeDualizingSheaf.mk

/-- The canonical affine identification attached to the chosen presentation of a relative
dualizing sheaf. -/
def chosenSectionIso (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U) :
    (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).obj W.module.obj ≅
      (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) :=
  W.sectionIso U V hVU

/-- The affine identification on the actual pulled-back base principal pair, transported to
the canonical simultaneously localized presentation. -/
noncomputable def principalSectionIso (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    principalSections W.module.obj V ((f.appLE U V hVU).hom a) ≅
      (W.presentation U V hVU).awayModuleRestricted
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) a :=
  (ModuleCat.restrictScalars
      (Y.presheaf.map
        (homOfLE (X := Y.Opens)
          (Y.affineBasicOpen_le ((f.appLE U V hVU).hom a))).op).hom).mapIso
      (W.sectionIso (X.affineBasicOpen a)
        (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
        (affineBasicOpen_le_preimage f U V hVU a)) ≪≫
    W.basePrincipalComparison U V hVU a

/-- The affine identification on an actual target principal open, transported through the
canonical comparison governed by `RelativeDualizingModule.awayTargetIso`. -/
noncomputable def targetPrincipalSectionIso (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (b : Γ(Y, V)) :
    principalSections W.module.obj V b ≅
      (W.presentation U V hVU).awayTargetModuleRestricted
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) b :=
  (ModuleCat.restrictScalars
      (Y.presheaf.map
        (homOfLE (X := Y.Opens) (Y.affineBasicOpen_le b)).op).hom).mapIso
      (W.sectionIso U (Y.affineBasicOpen b)
        (affineBasicOpen_target_le f U V hVU b)) ≪≫
    W.targetPrincipalComparison U V hVU b

/-- The prescribed canonical transition between chosen affine models. -/
noncomputable def transition (W : RelativeDualizingSheaf f)
    (U U' : X.affineOpens) (hU : U' ≤ U)
    (V V' : Y.affineOpens) (hV : V' ≤ V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U') :
    (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) →ₛₗ[
          (Y.presheaf.map (homOfLE (X := Y.Opens) hV).op).hom]
      (W.presentation U' V' hVU').module
        (IsLocallyNoetherian.component_noetherian U')
        (IsLocallyNoetherian.component_noetherian V')
        (affineQuasiFinite f U' V' hVU') :=
  W.restrictionComparison U U' hU V V' hV hVU hVU'

/-- Chosen-model transition is natural with respect to restriction of sheaf sections. -/
theorem transition_naturality (W : RelativeDualizingSheaf f)
    (U U' : X.affineOpens) (hU : U' ≤ U)
    (V V' : Y.affineOpens) (hV : V' ≤ V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U')
    (s : Γ(W.module.obj, V)) :
    transition f W U U' hU V V' hV hVU hVU'
        ((W.sectionIso U V hVU).hom s) =
      (W.sectionIso U' V' hVU').hom
        (restrictSections W.module.obj V V' hV s) := sorry

/-- The prescribed transition for an identity inclusion is the identity map. -/
theorem transition_id (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (x : (W.presentation U V hVU).module
      (IsLocallyNoetherian.component_noetherian U)
      (IsLocallyNoetherian.component_noetherian V)
      (affineQuasiFinite f U V hVU)) :
    transition f W U U le_rfl V V le_rfl hVU hVU x = x := sorry

/-- Chosen-model transitions along two successive affine restrictions satisfy the cocycle
law. -/
theorem transition_comp (W : RelativeDualizingSheaf f)
    (U₀ U₁ U₂ : X.affineOpens) (hU₀₁ : U₁ ≤ U₀) (hU₁₂ : U₂ ≤ U₁)
    (hU₀₂ : U₂ ≤ U₀) (V₀ V₁ V₂ : Y.affineOpens)
    (hV₀₁ : V₁ ≤ V₀) (hV₁₂ : V₂ ≤ V₁) (hV₀₂ : V₂ ≤ V₀)
    (hV₀U₀ : V₀ ≤ f ⁻¹ᵁ U₀) (hV₁U₁ : V₁ ≤ f ⁻¹ᵁ U₁)
    (hV₂U₂ : V₂ ≤ f ⁻¹ᵁ U₂)
    (x : (W.presentation U₀ V₀ hV₀U₀).module
      (IsLocallyNoetherian.component_noetherian U₀)
      (IsLocallyNoetherian.component_noetherian V₀)
      (affineQuasiFinite f U₀ V₀ hV₀U₀)) :
    transition f W U₁ U₂ hU₁₂ V₁ V₂ hV₁₂ hV₁U₁ hV₂U₂
        (transition f W U₀ U₁ hU₀₁ V₀ V₁ hV₀₁ hV₀U₀ hV₁U₁ x) =
      transition f W U₀ U₂ hU₀₂ V₀ V₂ hV₀₂ hV₀U₀ hV₂U₂ x := sorry

/-- An affine identification with another explicit model is obtained from the chosen one by
the canonical presentation comparison. -/
def sectionComparison (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (P : Algebra.RelativeDualizingModule.Presentation (f.appLE U V hVU))
    (i : @AlgHom Γ(X, U) P.finiteModel
      (W.presentation U V hVU).finiteModel _ _ _
      P.toFinite.hom.toAlgebra (W.presentation U V hVU).toFinite.hom.toAlgebra)
    (htriangle : (W.presentation U V hVU).toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P
        (W.presentation U V hVU) i) = P.toTarget.hom) :
    (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).obj W.module.obj ⟶
      P.module (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) :=
  (W.sectionIso U V hVU).hom ≫
    Algebra.RelativeDualizingModule.Presentation.comparison P
      (W.presentation U V hVU)
      (IsLocallyNoetherian.component_noetherian U)
      (IsLocallyNoetherian.component_noetherian V)
      (affineQuasiFinite f U V hVU) i htriangle

/-- Affine identifications are independent of a chain of refinements: direct comparison
agrees with successive canonical presentation comparisons. -/
theorem sectionComparison_comp (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (P₀ P₁ : Algebra.RelativeDualizingModule.Presentation (f.appLE U V hVU))
    (i₀₁ : @AlgHom Γ(X, U) P₀.finiteModel P₁.finiteModel _ _ _
      P₀.toFinite.hom.toAlgebra P₁.toFinite.hom.toAlgebra)
    (i₁ : @AlgHom Γ(X, U) P₁.finiteModel
      (W.presentation U V hVU).finiteModel _ _ _
      P₁.toFinite.hom.toAlgebra (W.presentation U V hVU).toFinite.hom.toAlgebra)
    (htriangle₀₁ : P₁.toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P₀ P₁ i₀₁) =
        P₀.toTarget.hom)
    (htriangle₁ : (W.presentation U V hVU).toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P₁
        (W.presentation U V hVU) i₁) = P₁.toTarget.hom)
    (htriangle₀ : (W.presentation U V hVU).toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P₀
        (W.presentation U V hVU)
        (Algebra.RelativeDualizingModule.Presentation.refinementComp P₀ P₁
          (W.presentation U V hVU) i₀₁ i₁)) = P₀.toTarget.hom) :
    sectionComparison f W U V hVU P₀
        (Algebra.RelativeDualizingModule.Presentation.refinementComp P₀ P₁
          (W.presentation U V hVU) i₀₁ i₁) htriangle₀ =
      sectionComparison f W U V hVU P₁ i₁ htriangle₁ ≫
        Algebra.RelativeDualizingModule.Presentation.comparison P₀ P₁
          (IsLocallyNoetherian.component_noetherian U)
          (IsLocallyNoetherian.component_noetherian V)
          (affineQuasiFinite f U V hVU) i₀₁ htriangle₀₁ := sorry

/-- Actual principal-open restriction is carried by the chosen affine identification to the
canonical map whose localization comparison is `Presentation.awayModuleIso`. -/
theorem principalRestriction_awayModuleIso (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (s : Γ(W.module.obj, V)) :
    (principalSectionIso f W U V hVU a).hom
        (restrictSectionsLinear W.module.obj V
          (Y.affineBasicOpen ((f.appLE U V hVU).hom a))
          (Y.affineBasicOpen_le ((f.appLE U V hVU).hom a)) s) =
      (W.presentation U V hVU).awayRestrictionLinear
        (IsLocallyNoetherian.component_noetherian U)
          (IsLocallyNoetherian.component_noetherian V)
          (affineQuasiFinite f U V hVU) a
        ((W.sectionIso U V hVU).hom s) := sorry

/-- Actual restriction to a target principal open is carried by the smaller affine-pair
identification to the canonical map defined by `RelativeDualizingModule.awayTargetIso`. -/
theorem targetPrincipalRestriction_awayTargetIso (W : RelativeDualizingSheaf f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (b : Γ(Y, V)) (s : Γ(W.module.obj, V)) :
    (targetPrincipalSectionIso f W U V hVU b).hom
        (restrictSectionsLinear W.module.obj V (Y.affineBasicOpen b)
          (Y.affineBasicOpen_le b) s) =
      (W.presentation U V hVU).awayTargetRestrictionLinear
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) b
        ((W.sectionIso U V hVU).hom s) := sorry

/-- A module-sheaf isomorphism induces an isomorphism on sections of an affine open. -/
def sectionsIso {M N : Y.Modules} (i : M ≅ N) (V : Y.affineOpens) :
    (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).obj M ≅
      (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).obj N :=
  (RingedSpace.moduleSectionsEvaluationFunctor Y.toRingedSpace V).mapIso i

/-- The isomorphism between chosen affine models induced by a sheaf isomorphism and the two
stored affine identifications. -/
def modelIso (W W' : RelativeDualizingSheaf f)
    (i : W.module.obj ≅ W'.module.obj) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U) :
    (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) ≅
      (W'.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f U V hVU) :=
  (W.sectionIso U V hVU).symm ≪≫ sectionsIso i V ≪≫
    W'.sectionIso U V hVU

/-- A sheaf isomorphism preserves every affine identification after canonical comparison of
finite/open presentations. -/
def PreservesAffineIdentifications (W W' : RelativeDualizingSheaf f)
    (i : W.module.obj ≅ W'.module.obj) : Prop :=
  ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U)
    (P : Algebra.RelativeDualizingModule.Presentation (f.appLE U V hVU))
    (j : @AlgHom Γ(X, U) P.finiteModel
      (W.presentation U V hVU).finiteModel _ _ _
      P.toFinite.hom.toAlgebra (W.presentation U V hVU).toFinite.hom.toAlgebra)
    (j' : @AlgHom Γ(X, U) P.finiteModel
      (W'.presentation U V hVU).finiteModel _ _ _
      P.toFinite.hom.toAlgebra (W'.presentation U V hVU).toFinite.hom.toAlgebra)
    (htriangle : (W.presentation U V hVU).toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P
        (W.presentation U V hVU) j) = P.toTarget.hom)
    (htriangle' : (W'.presentation U V hVU).toTarget.hom.comp
      (Algebra.RelativeDualizingModule.Presentation.refinementRingHom P
        (W'.presentation U V hVU) j') = P.toTarget.hom),
    (sectionsIso i V).hom ≫
        sectionComparison f W' U V hVU P j' htriangle' =
      sectionComparison f W U V hVU P j htriangle

/-- A sheaf isomorphism intertwines the prescribed canonical transitions on all nested
compatible affine pairs. -/
def PreservesTransitions (W W' : RelativeDualizingSheaf f)
    (i : W.module.obj ≅ W'.module.obj) : Prop :=
  ∀ (U U' : X.affineOpens) (hU : U' ≤ U)
    (V V' : Y.affineOpens) (hV : V' ≤ V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U')
    (x : (W.presentation U V hVU).module
      (IsLocallyNoetherian.component_noetherian U)
      (IsLocallyNoetherian.component_noetherian V)
      (affineQuasiFinite f U V hVU)),
    transition f W' U U' hU V V' hV hVU hVU'
        ((modelIso f W W' i U V hVU).hom x) =
      (modelIso f W W' i U' V' hVU').hom
        (transition f W U U' hU V V' hV hVU hVU' x)

/-- A sheaf isomorphism is compatible when it preserves both the canonical affine
identifications and their prescribed restriction-transition system. -/
def Compatible (W W' : RelativeDualizingSheaf f)
    (i : W.module.obj ≅ W'.module.obj) : Prop :=
  PreservesAffineIdentifications f W W' i ∧ PreservesTransitions f W W' i

/-- Compatibility of a sheaf isomorphism is exactly preservation of affine identifications
and of every prescribed canonical transition. -/
theorem compatible_iff (W W' : RelativeDualizingSheaf f)
    (i : W.module.obj ≅ W'.module.obj) :
    Compatible f W W' i ↔
      PreservesAffineIdentifications f W W' i ∧
        PreservesTransitions f W W' i := sorry

/-- The defining specification exposes coherence and compatibility of every affine
identification with the prescribed canonical restriction maps. -/
theorem spec (W : RelativeDualizingSheaf f) :
    W.module.obj.IsCoherent ∧
      ∀ (U U' : X.affineOpens) (hU : U' ≤ U)
        (V V' : Y.affineOpens) (hV : V' ≤ V)
        (hVU : V ≤ f ⁻¹ᵁ U) (hVU' : V' ≤ f ⁻¹ᵁ U')
        (s : Γ(W.module.obj, V)),
        transition f W U U' hU V V' hV hVU hVU'
            ((W.sectionIso U V hVU).hom s) =
          (W.sectionIso U' V' hVU').hom
            (restrictSections W.module.obj V V' hV s) := sorry

/-- A locally finite-type and locally quasi-finite morphism between locally Noetherian schemes
admits a relative dualizing sheaf, unique up to a unique compatible isomorphism. -/
theorem existsUnique :
    ∃ W : RelativeDualizingSheaf f,
      ∀ W' : RelativeDualizingSheaf f,
        ∃! i : W.module.obj ≅ W'.module.obj, Compatible f W W' i := sorry

end RelativeDualizingSheaf

end AlgebraicGeometry.Scheme.Hom
