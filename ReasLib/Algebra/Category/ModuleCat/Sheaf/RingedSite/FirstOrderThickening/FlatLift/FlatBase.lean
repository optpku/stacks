/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatKernel
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift.IsoClass
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Lift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction

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

/-- Over a strict flat thickening square, a relatively flat module has a flat lift
exactly when its Ext² obstruction with pulled-back base-ideal coefficients vanishes. -/
theorem exists_flatOver_iff_of_isFlatHom [IsFlat OB ((restrictionAlong f).obj F)]
    [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O')]
    [hstrict : Epi (kernelPullbackMap f f' hcomm)]
    [hflat : IsFlat OB' ((restrictionAlong f').obj (unitModule J O'))] :
    Nonempty (FlatLift π f' F) ↔
      ModuleExtension.existenceObstruction π F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F)
        (inv (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F))) = 0 := sorry

namespace FlatLift

/-- An automorphism of a flat lift pulling back to `𝟙 F` is a lift of the identity on
`i^* F'`. -/
theorem toIdLift_comm (L : FlatLift π f' F) (φ : Hom L L) :
    CommSq φ.hom (extendRestrictUnit π L.module) (extendRestrictUnit π L.module)
      ((restrictionAlong π).map
        (𝟙 ((extendScalars (ringSheafMap π)).obj L.module))) := sorry

/-- A compatible automorphism of a flat lift induces a lift of the identity on its reduction. -/
def toIdLift (L : FlatLift π f' F) (φ : Hom L L) :
    Lift L.module L.module (𝟙 ((extendScalars (ringSheafMap π)).obj L.module)) :=
  Lift.of L.module L.module (𝟙 ((extendScalars (ringSheafMap π)).obj L.module))
    φ.hom (toIdLift_comm f' F L φ)

/-- The underlying morphism of `toIdLift` is the automorphism of the middle module. -/
theorem toIdLift_hom (L : FlatLift π f' F) (φ : Hom L L) :
    (toIdLift f' F L φ).hom = φ.hom := sorry

/-- When a flat lift exists, its isomorphism classes form a principal homogeneous space
under Ext¹ with pulled-back base-ideal coefficients, via the Baer-sum action. -/
theorem isoClass_principalHomogeneous_of_isFlatHom
    [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f')
    (h_exists : Nonempty (FlatLift π f' F)) (E E' : IsoClass π f' F) :
    ∃! x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 1,
      ∀ ξ : ExtensionClass (moduleTensor (ideal π) F) F,
        ExtensionClass.toExt ξ =
            (Ext.mk₀ (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F))).postcomp F
              (add_zero 1) x ↔
          vadd hstrict ξ E = E' := sorry

/-- Canonical correspondence between an automorphism of a given flat lift pulling
back to `𝟙 F` and an `Ext 0` class with coefficients `f^* J ⊗_O F`. -/
def autExt0Rel (L : FlatLift π f' F) (φ : Hom L L)
    (x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0) :
    Prop :=
  ∀ α : (extendScalars (ringSheafMap π)).obj L.module ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj L.module),
    Ext.mk₀
        (inv L.isoHom (I := L.isoHom_isIso) ≫
          α ≫ moduleTensorMap
            (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) L.isoHom) = x ↔
      ∃ β : L.module ⟶ idealMulO' π L.module,
        (extendScalars (ringSheafMap π)).map β =
            α ≫ canonicalMap π f f' hcomm L.module ∧
          Lift.vadd L.module L.module
              (𝟙 ((extendScalars (ringSheafMap π)).obj L.module)) β
              (toIdLift f' F L (Hom.id L)) =
            toIdLift f' F L φ

/-- Compatible automorphisms of a fixed flat lift correspond bijectively to Ext⁰
with pulled-back base-ideal coefficients through identity-based translation. -/
theorem aut_existsUnique_ext0 [IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f')
    (L : FlatLift π f' F) :
    (∀ φ : Hom L L,
        ∃! x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0,
          autExt0Rel f f' hcomm F L φ x) ∧
      (∀ x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0,
        ∃! φ : Hom L L, autExt0Rel f f' hcomm F L φ x) := sorry

end FlatLift

end SheafOfModules.RingedSite.FirstOrderThickening
