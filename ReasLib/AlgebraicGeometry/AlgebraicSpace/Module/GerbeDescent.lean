/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.CategoryTheory.Fibered.Gerbe.Basic
public import ReasLib.CategoryTheory.Sites.Module.LocalActionDescent
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Scalar descent on the additive sheaf of a gerbe

The index presheaf consists of actual fiberwise isomorphism classes of the gerbe. Its local
terminal property permits descent of specified local scalar operations. Restriction to the
small étale site keeps the additive sections of the given global sheaf.
-/

@[expose] public section

open CategoryTheory Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.GerbeModuleDescent

variable {S : Scheme.{u}} (W : AlgebraicSpace S)
variable {D : Type (u + 1)} [Category.{u + 1} D]
variable (p : D ⥤ spacesEtaleSite W) [IsGerbe (spacesEtaleTopology W) p]

/-- Actual isomorphism classes of lifts, restricted to the genuine presentation small site. -/
def indices : (smallEtaleSite W)ᵒᵖ ⥤ Type (u + 1) :=
  (smallEtaleToSpaces W).op ⋙ Functor.fiberIsoClassPresheaf p

/-- Local inhabitedness of the gerbe supplies local class representatives on small charts. -/
instance indices_locallySurjective :
    Presheaf.IsLocallySurjective (smallEtaleTopology W) (Limits.terminal.from (indices W p)) := by
  let η := (smallEtaleToSpaces W).op.whiskerLeft
    (Limits.terminal.from (Functor.fiberIsoClassPresheaf p))
  letI : Presheaf.IsLocallySurjective (smallEtaleTopology W) η :=
    Presheaf.isLocallySurjective_whisker (smallEtaleTopology W) (spacesEtaleTopology W)
      (smallEtaleToSpaces W) (Limits.terminal.from (Functor.fiberIsoClassPresheaf p))
  let τ := Limits.terminal.from
    ((smallEtaleToSpaces W).op ⋙ (⊤_ ((spacesEtaleSite W)ᵒᵖ ⥤ Type (u + 1))))
  letI : IsIso τ := Limits.isIso_of_isTerminal
    (Limits.isLimitOfHasTerminalOfPreservesLimit
      ((Functor.whiskeringLeft (smallEtaleSite W)ᵒᵖ (spacesEtaleSite W)ᵒᵖ (Type (u + 1))).obj
        (smallEtaleToSpaces W).op)) Limits.terminalIsTerminal τ
  have hterminal : η ≫ τ = Limits.terminal.from (indices W p) :=
    Limits.terminal.comp_from η
  rw [← hterminal]
  exact Presheaf.isLocallySurjective_comp (smallEtaleTopology W) η τ

/-- Local connectedness of the gerbe identifies its local class representatives. -/
instance indices_locallyInjective :
    Presheaf.IsLocallyInjective (smallEtaleTopology W) (Limits.terminal.from (indices W p)) := by
  let η := (smallEtaleToSpaces W).op.whiskerLeft
    (Limits.terminal.from (Functor.fiberIsoClassPresheaf p))
  letI : Presheaf.IsLocallyInjective (smallEtaleTopology W) η :=
    Presheaf.isLocallyInjective_whisker (smallEtaleTopology W) (spacesEtaleTopology W)
      (smallEtaleToSpaces W) (Limits.terminal.from (Functor.fiberIsoClassPresheaf p))
  let τ := Limits.terminal.from
    ((smallEtaleToSpaces W).op ⋙ (⊤_ ((spacesEtaleSite W)ᵒᵖ ⥤ Type (u + 1))))
  letI : IsIso τ := Limits.isIso_of_isTerminal
    (Limits.isLimitOfHasTerminalOfPreservesLimit
      ((Functor.whiskeringLeft (smallEtaleSite W)ᵒᵖ (spacesEtaleSite W)ᵒᵖ (Type (u + 1))).obj
        (smallEtaleToSpaces W).op)) Limits.terminalIsTerminal τ
  have hterminal : η ≫ τ = Limits.terminal.from (indices W p) :=
    Limits.terminal.comp_from η
  rw [← hterminal]
  exact Presheaf.isLocallyInjective_comp (smallEtaleTopology W) η τ

/-- Restrict the given global additive sheaf using the actual presentation inclusion. -/
def additiveRestriction (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1} :=
  ((smallEtaleToSpaces W).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology W) (spacesEtaleTopology W)).obj G

/-- Genuine limits supply the additive right Kan extension on the presentation inclusion. -/
instance additiveRightKan (Q : (smallEtaleSite W)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtaleToSpaces W).op.HasPointwiseRightKanExtension Q :=
  fun _ ↦ inferInstance

/-- Extend the actual additive sections from presentation charts by native right Kan limits. -/
def additiveExtension :
    Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1} ⥤
      Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1} :=
  (smallEtaleToSpaces W).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology W) (spacesEtaleTopology W)

private theorem additiveExtensionComparison_unit_comp
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}) :
    ((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology W) (spacesEtaleTopology W)).unit.app G ≫
      (⟨Functor.IsCoverDense.sheafHom
        (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology W) (spacesEtaleTopology W)).counit.app
            (additiveRestriction W G)).hom⟩ :
        (additiveExtension W).obj (additiveRestriction W G) ⟶ G) = 𝟙 G := by
  apply ((smallEtaleToSpaces W).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology W) (spacesEtaleTopology W)).map_injective
  apply Sheaf.hom_ext
  change Functor.whiskerLeft (smallEtaleToSpaces W).op
      (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology W) (spacesEtaleTopology W)).unit.app G).hom ≫
    Functor.whiskerLeft (smallEtaleToSpaces W).op (Functor.IsCoverDense.sheafHom
      (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology W) (spacesEtaleTopology W)).counit.app
          (additiveRestriction W G)).hom) = 𝟙 _
  rw [Functor.IsCoverDense.sheafHom_restrict_eq]
  exact congrArg (fun f ↦ f.hom)
    (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology W) (spacesEtaleTopology W)).left_triangle_components G)

/-- Extension of the restriction has the actual chartwise counit glued into `G`. The reverse
map is the native right-Kan adjunction unit, not an inverse chosen from an invertibility law. -/
def additiveExtensionComparison
    (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (additiveExtension W).obj (additiveRestriction W G) ≅ G where
  hom := ⟨Functor.IsCoverDense.sheafHom
    (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology W) (spacesEtaleTopology W)).counit.app (additiveRestriction W G)).hom⟩
  inv := ((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology W) (spacesEtaleTopology W)).unit.app G
  hom_inv_id := by
    have h := additiveExtensionComparison_unit_comp W G
    haveI : IsSplitEpi
        (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology W) (spacesEtaleTopology W)).unit.app G) :=
      Adjunction.unit_isSplitEpi_of_L_full _ G
    apply (cancel_epi
      (((smallEtaleToSpaces W).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology W) (spacesEtaleTopology W)).unit.app G)).mp
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ _) h).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm))
  inv_hom_id := by
    exact additiveExtensionComparison_unit_comp W G

/-- The local operations required for descent are functions on the actual restricted band
sections, indexed by the gerbe's fiberwise classes. -/
abbrev LocalAction (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1}) :=
  Sheaf.LocalActionDescent.LocalAction (smallEtaleTopology W)
    (commRingedSiteLift W).structureSheaf (additiveRestriction W G) (indices W p)

section LocalComparisons

variable (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
variable (V : ∀ T : (smallEtaleSite W)ᵒᵖ, (indices W p).obj T →
  ModuleCat.{u + 1} ((commRingedSiteLift W).structureSheaf.obj.obj T))
variable (e : ∀ T i, (additiveRestriction W G).obj.obj T ≃+ V T i)

/-- Transport a scalar through the two specified functions of an actual local additive
comparison, apply the scalar on the local parameter module, and return to the band section. -/
def scalarFromComparison (T : (smallEtaleSite W)ᵒᵖ) (i : (indices W p).obj T)
    (r : (commRingedSiteLift W).structureSheaf.obj.obj T)
    (g : (additiveRestriction W G).obj.obj T) : (additiveRestriction W G).obj.obj T :=
  (e T i).symm (r • e T i g)

/-- The local scalar operation is fixed by the actual comparison functions. -/
@[simp]
theorem scalarFromComparison_apply (T : (smallEtaleSite W)ᵒᵖ) (i : (indices W p).obj T)
    (r : (commRingedSiteLift W).structureSheaf.obj.obj T)
    (g : (additiveRestriction W G).obj.obj T) :
    scalarFromComparison W p G V e T i r g = (e T i).symm (r • e T i g) := rfl

/-- Conjugation-compatible local comparisons give the concrete local action used by descent.
Only restriction compatibility is a premise; all operation data come from the supplied local
modules and the two supplied comparison functions. -/
def localActionOfComparisons
    (h : ∀ {T U : (smallEtaleSite W)ᵒᵖ} (f : T ⟶ U)
      (i : (indices W p).obj T)
      (r : (commRingedSiteLift W).structureSheaf.obj.obj T)
      (g : (additiveRestriction W G).obj.obj T),
      (additiveRestriction W G).obj.map f (scalarFromComparison W p G V e T i r g) =
        scalarFromComparison W p G V e U ((indices W p).map f i)
          ((commRingedSiteLift W).structureSheaf.obj.map f r)
          ((additiveRestriction W G).obj.map f g)) : LocalAction W p G where
  smul := scalarFromComparison W p G V e
  naturality := h
  one_smul := by
    intro T i g
    simp [scalarFromComparison]
  mul_smul := by
    intro T i r s g
    simp [scalarFromComparison, mul_smul]
  smul_add := by
    intro T i r g₁ g₂
    simp [scalarFromComparison, smul_add]
  smul_zero := by
    intro T i r
    simp [scalarFromComparison]
  add_smul := by
    intro T i r s g
    simp [scalarFromComparison, add_smul]
  zero_smul := by
    intro T i g
    simp [scalarFromComparison]

end LocalComparisons

/-- Descend the supplied concrete local operations by native sheaf amalgamation. -/
def module (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (A : LocalAction W p G) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift W) :=
  Sheaf.LocalActionDescent.module (smallEtaleTopology W)
    (commRingedSiteLift W).structureSheaf (additiveRestriction W G) (indices W p) A

/-- The additive sections are unchanged by the module descent. Both maps are identity maps. -/
def underlyingIso (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (A : LocalAction W p G) :
    (SheafOfModules.toSheaf (commRingedSiteLift W).structureSheaf).obj (module W p G A) ≅
      additiveRestriction W G :=
  Sheaf.LocalActionDescent.underlyingIso (smallEtaleTopology W)
    (commRingedSiteLift W).structureSheaf (additiveRestriction W G) (indices W p) A

/-- The underlying global band comparison uses the identity small-chart comparison, the
actual extension functor, and the two specified descent/adjunction maps. -/
def spacesUnderlyingIso (G : Sheaf (spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (A : LocalAction W p G) :
    (additiveExtension W).obj
      ((SheafOfModules.toSheaf (commRingedSiteLift W).structureSheaf).obj (module W p G A)) ≅ G :=
  (additiveExtension W).mapIso (underlyingIso W p G A) ≪≫ additiveExtensionComparison W G

end AlgebraicGeometry.AlgebraicSpace.GerbeModuleDescent
