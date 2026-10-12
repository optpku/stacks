/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_10_4_Obstruction
public import stacks_project.Chap91.Lemma_91_11_1_Lift
public import stacks_project.Chap91.Lemma_91_11_2_Canonical
public import stacks_project.Chap91.Lemma_91_11_7_IsoClass
public import stacks_project.Chap91.Lemma_91_11_7_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat modules on flat first-order thickenings of ringed topoi

In the square of first-order thickenings of ringed topoi from section 91.12, if
`(f, f')` is strict, `f'` is flat, and `F` is flat over `O_B`, then `I = f^* J`
and the existence, isomorphism-class, and automorphism theories of flat lifts of
`F` are governed by `Ext F (f^* J ⊗_O F) n` for `n = 2, 1, 0`.
-/

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

/-- Strictness of `(f, f')` together with flatness of `f'` identifies `I` with `f^* J`. -/
theorem kernelPullbackMap_isIso (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f') :
    IsIso (kernelPullbackMap f f' hcomm) := sorry

/-- Tensoring the kernel-pullback comparison with `F` is an isomorphism. -/
theorem moduleTensor_kernelPullback_isIso (hstrict : IsStrict f f' hcomm)
    (hflat : IsFlatHom f') :
    IsIso (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F)) := sorry

/-- Lemma 91.12.1 (1): There exists an `O'`-module `F'` flat over `O_{B'}` with
`i^* F' ≅ F` if and only if the class `o(F, f^* J ⊗_O F, 1)` in
`Ext F (f^* J ⊗_O F) 2` of Lemma 91.10.4 is zero. -/
@[stacks 08VW]
theorem exists_flatOver_iff_of_isFlatHom [IsFlat OB ((restrictionAlong f).obj F)]
    [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O')]
    (hstrict : IsStrict f f' hcomm) (hflat : IsFlatHom f') :
    Nonempty (FlatLift π f' F) ↔
      ModuleExtension.obstruction π F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F)
        (@inv _ _ _ _ (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F))
          (moduleTensor_kernelPullback_isIso f f' hcomm F hstrict hflat)) = 0 := sorry

namespace FlatLift

/-- The identity on the middle module of a flat lift is compatible with the comparison
morphism. -/
theorem idHom_comm (L : FlatLift π f' F) :
    L.isoHom = (extendScalars (ringSheafMap π)).map (𝟙 L.module) ≫ L.isoHom := sorry

/-- The identity automorphism of a flat lift. -/
def idHom (L : FlatLift π f' F) : Hom L L :=
  Hom.of (𝟙 L.module) (idHom_comm f' F L) (IsIso.id L.module)

/-- The underlying morphism of `idHom` is the identity on the middle module. -/
theorem idHom_hom (L : FlatLift π f' F) : (idHom f' F L).hom = 𝟙 L.module := sorry

/-- An automorphism of a flat lift pulling back to `𝟙 F` is a lift of the identity on
`i^* F'`. -/
theorem toIdLift_comm (L : FlatLift π f' F) (φ : Hom L L) :
    CommSq φ.hom (extendRestrictUnit π L.module) (extendRestrictUnit π L.module)
      ((restrictionAlong π).map
        (𝟙 ((extendScalars (ringSheafMap π)).obj L.module))) := sorry

/-- View an automorphism of a flat lift as a Lemma 91.11.1 lift of the identity on
`i^* F'`. -/
def toIdLift (L : FlatLift π f' F) (φ : Hom L L) :
    Lift L.module L.module (𝟙 ((extendScalars (ringSheafMap π)).obj L.module)) :=
  Lift.of L.module L.module (𝟙 ((extendScalars (ringSheafMap π)).obj L.module))
    φ.hom (toIdLift_comm f' F L φ)

/-- The underlying morphism of `toIdLift` is the automorphism of the middle module. -/
theorem toIdLift_hom (L : FlatLift π f' F) (φ : Hom L L) :
    (toIdLift f' F L φ).hom = φ.hom := sorry

/-- Lemma 91.12.1 (2): If such a module exists, then the set of isomorphism classes of
lifts is principal homogeneous under `Ext F (f^* J ⊗_O F) 1`. -/
@[stacks 08VW]
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
        (@inv _ _ _ _ L.isoHom L.isoHom_isIso ≫
          α ≫ moduleTensorMap
            (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) L.isoHom) = x ↔
      ∃ β : L.module ⟶ idealMulO' π L.module,
        (extendScalars (ringSheafMap π)).map β =
            α ≫ canonicalMap π f f' hcomm L.module ∧
          Lift.vadd L.module L.module
              (𝟙 ((extendScalars (ringSheafMap π)).obj L.module)) β
              (toIdLift f' F L (idHom f' F L)) =
            toIdLift f' F L φ

/-- `autExt0Rel` is the conjugation/`Lift.vadd` matching of `Ext.mk₀` classes with
automorphisms based at `idHom`. -/
theorem autExt0Rel_iff (L : FlatLift π f' F) (φ : Hom L L)
    (x : Ext F (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ)) F) 0) :
    autExt0Rel f f' hcomm F L φ x ↔
      (∀ α : (extendScalars (ringSheafMap π)).obj L.module ⟶
          moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
            ((extendScalars (ringSheafMap π)).obj L.module),
        Ext.mk₀
            (@inv _ _ _ _ L.isoHom L.isoHom_isIso ≫
              α ≫ moduleTensorMap
                (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) L.isoHom) = x ↔
          ∃ β : L.module ⟶ idealMulO' π L.module,
            (extendScalars (ringSheafMap π)).map β =
                α ≫ canonicalMap π f f' hcomm L.module ∧
              Lift.vadd L.module L.module
                  (𝟙 ((extendScalars (ringSheafMap π)).obj L.module)) β
                  (toIdLift f' F L (idHom f' F L)) =
                toIdLift f' F L φ) := sorry

/-- Lemma 91.12.1 (3): Given a lift `F'`, the set of automorphisms of `F'` which pull
back to `𝟙 F` is canonically isomorphic to `Ext F (f^* J ⊗_O F) 0`. -/
@[stacks 08VW]
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
