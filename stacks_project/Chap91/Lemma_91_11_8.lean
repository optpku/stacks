module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatExistence
import StacksCheckRecall

/-!
# Existence of a flat lift across a strict morphism of first-order thickenings

After identifying underlying topoi, a strict morphism of first-order thickenings as in
Situation 91.9.1 admits an `O'`-module `F'` flat over `O_{B'}` with `i^* F' ≅ F` if and
only if `f^* J ⊗_O F ⟶ I ⊗_O F` is invertible and the Lemma 91.10.4 class
`o(F, I ⊗_O F, 1)` vanishes.
-/

@[expose] public section

open CategoryTheory
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
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O')]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/- Lemma 91.11.8: Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.9.1. Let `F` be an `O`-module. Assume `(f, f')` is a strict morphism of
thickenings and `F` is flat over `O_B`. There exists an `O'`-module `F'` flat over
`O_{B'}` with `i^* F' ≅ F` if and only if the canonical map `f^* J ⊗_O F ⟶ I ⊗_O F`
is an isomorphism and the class `o(F, I ⊗_O F, 1)` in `Ext^2_O(F, I ⊗_O F)` of
Lemma 91.10.4 is zero. -/
@[stacks 08MV] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.exists_flatOver_iff f f' hcomm F :
    ∀ [hflat : IsFlat OB ((restrictionAlong f).obj F)], IsStrict f f' hcomm →
    ((∃ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
        IsFlat OB' ((restrictionAlong f').obj F') ∧
          Nonempty ((extendScalars (ringSheafMap π)).obj F' ≅ F)) ↔
      IsIso (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F)) ∧
        ModuleExtension.existenceObstruction π F (moduleTensor (ideal π) F)
          (𝟙 (moduleTensor (ideal π) F)) = 0))

end SheafOfModules.RingedSite.FirstOrderThickening
