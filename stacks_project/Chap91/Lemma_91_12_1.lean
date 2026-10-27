/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift.FlatBase
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian (Ext)
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/- Lemma 91.12.1 (1): Flat lifts exist exactly when the canonical Ext² obstruction vanishes. -/
@[stacks 08VW] #check (SheafOfModules.RingedSite.FirstOrderThickening.exists_flatOver_iff_of_isFlatHom f f' hcomm F :
    ∀ [IsFlat OB ((restrictionAlong f).obj F)]
    [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O')]
    [hstrict : Epi (kernelPullbackMap f f' hcomm)]
    [hflat : IsFlat OB' ((restrictionAlong f').obj (unitModule J O'))],
    Nonempty (FlatLift π f' F) ↔
      ModuleExtension.existenceObstruction π F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F)
        (inv (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F))) = 0)

/- Lemma 91.12.1 (2): Isomorphism classes of flat lifts are principal homogeneous under Ext¹. -/
@[stacks 08VW] #check (SheafOfModules.RingedSite.FirstOrderThickening.FlatLift.isoClass_principalHomogeneous_of_isFlatHom f f' hcomm F :
    ∀ [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f')
    (h_exists : Nonempty (FlatLift π f' F)) (E E' : FlatLift.IsoClass π f' F),
    ∃! x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 1,
      ∀ ξ : ExtensionClass (moduleTensor (ideal π) F) F,
        ExtensionClass.toExt ξ =
            (Ext.mk₀ (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F))).postcomp F
              (add_zero 1) x ↔
          FlatLift.vadd hstrict ξ E = E')

/- Lemma 91.12.1 (3): Compatible automorphisms of a flat lift correspond canonically to Ext⁰. -/
@[stacks 08VW] #check (SheafOfModules.RingedSite.FirstOrderThickening.FlatLift.aut_existsUnique_ext0 f f' hcomm F :
    ∀ [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f')
    (L : FlatLift π f' F),
    (∀ φ : FlatLift.Hom L L,
        ∃! x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0,
          FlatLift.autExt0Rel f f' hcomm F L φ x) ∧
      (∀ x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0,
        ∃! φ : FlatLift.Hom L L, FlatLift.autExt0Rel f f' hcomm F L φ x))

end SheafOfModules.RingedSite.FirstOrderThickening
