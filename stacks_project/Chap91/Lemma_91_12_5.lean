/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismShortExact.Difference
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian (Ext)
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

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

namespace FlatMorphismShortExact

variable {O O_B O1' O2' O3' OB1' OB2' OB3' : Sheaf J CommRingCat.{max u v}}
variable {f : O_B ⟶ O} {π1 : O1' ⟶ O} {π2 : O2' ⟶ O} {π3 : O3' ⟶ O}
variable {τ1 : OB1' ⟶ O_B} {τ2 : OB2' ⟶ O_B} {τ3 : OB3' ⟶ O_B}
variable [hπ1 : IsFirstOrderThickening π1] [hπ2 : IsFirstOrderThickening π2]
variable [hπ3 : IsFirstOrderThickening π3]
variable [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
variable [IsFirstOrderThickening τ3]
variable [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable [(restrictScalars (ringSheafMap π1)).IsRightAdjoint]
variable [(restrictScalars (ringSheafMap π2)).IsRightAdjoint]
variable [(restrictScalars (ringSheafMap π3)).IsRightAdjoint]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/- Scalar extension along the diagram map is canonically isomorphic to its changed-scalar pushout. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.homPullbackIsoPushout :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint],
    homPullback S ≅ (homExtension S).module)

/- The scalar-extension comparison preserves the transported kernel inclusion. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.homPullbackIsoPushout_incl :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint],
    homPullbackIncl S ≫ (homPullbackIsoPushout S).hom = (homExtension S).incl)

/- The scalar-extension comparison preserves the adjunct quotient projection. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.homPullbackIsoPushout_proj :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint],
    (homPullbackIsoPushout S).hom ≫ (homExtension S).proj =
      extendRestrictHomEquiv (ringSheafMap π1) (homPullback S) (restrictModule S)
        (homPullbackRestrictIso S).hom)

/- The forward comparison is adjoint to the actual pushout middle-term leg. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.homPullbackIsoPushout_unit :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint],
    (extendRestrictAdjunction (ringSheafMap S.h.hom)).unit.app S.module ≫
        (restrictionAlong S.h.hom).map (homPullbackIsoPushout S).hom =
      homExtensionUnit S)

/- Lemma 91.12.5 (1) In Situation 91.12.4 the module `canonicalPullback S` is an
`O'_1`-module flat over `O_{B'_1}` restricting to `restrictModule S`. -/
@[stacks 08VY] #check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.canonicalPullback_restrict_isFlat :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint],
    IsFlat OB1' ((restrictionAlong S.f1').obj (canonicalPullback S)) ∧
      IsIso (canonicalPullbackRestrictIso S).hom)

/- Lemma 91.12.5 (2) In Situation 91.12.4 the module `homPullback S` is an
`O'_1`-module flat over `O_{B'_1}` restricting to `restrictModule S`. -/
@[stacks 08VY] #check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.homPullback_restrict_isFlat :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint],
    IsFlat OB1' ((restrictionAlong S.f1').obj (homPullback S)) ∧
      IsIso (homPullbackRestrictIso S).hom)

/- Lemma 91.12.5 (3) In Situation 91.12.4 the Lemma 91.12.1 difference of
`canonicalPullback S` and `homPullback S` is `difference S` in
`Ext (restrictModule S) (f^* J_1 ⊗ restrictModule S) 1`, and its connecting image
along `coeffShortComplex S` equals `obstruction3 S`, the obstruction to lifting
`restrictModule S` to an `O'_3`-module flat over `O_{B'_3}`. -/
@[stacks 08VY] #check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.difference_comp_eq_obstruction :
    ∀ (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O3')],
    (difference S).comp (coeff_shortExact S).extClass (rfl : 1 + 1 = 2) =
      obstruction3 S)

end FlatMorphismShortExact

end SheafOfModules.RingedSite.FirstOrderThickening
