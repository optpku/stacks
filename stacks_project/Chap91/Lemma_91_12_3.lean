module

public import stacks_project.Chap91.Remark_91_10_9
public import stacks_project.Chap91.Situation_91_12_2_Diagram
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of flat-module obstructions along a square of first-order thickenings

In Situation 91.12.2, Ext-postcomposition along `f^* J_2 ⊗ F ⟶ f^* J_1 ⊗ F` sends the
identity-infinitesimal obstruction on the second thickening to that on the first.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open CategoryTheory.MonoidalCategory
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace FlatMorphismSquare

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O O_B O1' O2' OB1' OB2' : Sheaf J CommRingCat.{max u v}}
variable {f : O_B ⟶ O} {π1 : O1' ⟶ O} {π2 : O2' ⟶ O}
variable {τ1 : OB1' ⟶ O_B} {τ2 : OB2' ⟶ O_B}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
variable [(restrictScalars (ringSheafMap f)).IsRightAdjoint]

/-- The canonical coefficient map `f^* J_2 ⊗_O F ⟶ f^* J_1 ⊗_O F` induced by the
base thickening morphism. -/
def pullbackIdealTensorMap (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2)) S.module ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1)) S.module :=
  moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base.idealMap) (𝟙 S.module)

/-- `pullbackIdealTensorMap` is the tensor morphism of `f^*` of the base ideal map with
`𝟙 F`. -/
theorem pullbackIdealTensorMap_eq (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    pullbackIdealTensorMap S =
      moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base.idealMap)
        (𝟙 S.module) := sorry

/-- Strictness of `(f, f'_1)` together with flatness of `f'_1` identifies `I_1` with
`f^* J_1`. -/
theorem idealMap_fst_isIso (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    IsIso S.idealMap_fst := sorry

/-- Strictness of `(f, f'_2)` together with flatness of `f'_2` identifies `I_2` with
`f^* J_2`. -/
theorem idealMap_snd_isIso (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    IsIso S.idealMap_snd := sorry

/-- The kernel-pullback comparisons, the base-induced coefficient map, and `h.idealMap`
form a commutative square after tensoring with `F`. -/
theorem pullbackIdealTensor_commSq (S : FlatMorphismSquare f π1 π2 τ1 τ2) :
    CommSq (moduleTensorMap S.idealMap_snd (𝟙 S.module)) (pullbackIdealTensorMap S)
      (moduleTensorMap S.h.idealMap (𝟙 S.module))
      (moduleTensorMap S.idealMap_fst (𝟙 S.module)) := sorry

/-- Lemma 91.12.3: In Situation 91.12.2, the obstruction class
`o(F, f^* J_2 ⊗_O F, 1)` in `Ext^2_O(F, f^* J_2 ⊗_O F)` is sent to
`o(F, f^* J_1 ⊗_O F, 1)` by Ext-postcomposition along `pullbackIdealTensorMap`.
Here `1` is the inverse of the kernel-tensor comparison `f^* J_i ⊗_O F ⟶ I_i ⊗_O F`. -/
@[stacks 0CYE]
theorem obstruction_map
    [HasSheafify J AddCommGrpCat.{max u v}]
    [(restrictScalars (ringSheafMap π1)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap π2)).IsRightAdjoint]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O1')]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O2')]
    [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    (S : FlatMorphismSquare f π1 π2 τ1 τ2)
    [IsIso S.idealMap_fst] [IsIso S.idealMap_snd] :
    (Ext.mk₀ (pullbackIdealTensorMap S)).postcomp S.module (add_zero 2)
        (ModuleExtension.obstruction π2 S.module
          (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2)) S.module)
          (inv (moduleTensorMap S.idealMap_snd (𝟙 S.module)))) =
      ModuleExtension.obstruction π1 S.module
        (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1)) S.module)
        (inv (moduleTensorMap S.idealMap_fst (𝟙 S.module))) := sorry

end FlatMorphismSquare
end SheafOfModules.RingedSite.FirstOrderThickening
