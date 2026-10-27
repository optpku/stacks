/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

@[expose] public section

open CategoryTheory CategoryTheory.Limits
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

/-- Restriction of scalars along a composite morphism of commutative ring sheaves is
the composite of the corresponding restriction functors. -/
noncomputable def restrictionAlongCompIso {𝒪₁ 𝒪₂ 𝒪₃ : Sheaf J CommRingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) (β : 𝒪₂ ⟶ 𝒪₃) :
    restrictionAlong (α ≫ β) ≅ restrictionAlong β ⋙ restrictionAlong α :=
  eqToIso (congrArg (fun t ↦ SheafOfModules.restrictScalars.{max u v} t)
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map_comp α β)) ≪≫
    (SheafOfModules.Restriction.compIso (ringSheafMap α) (ringSheafMap β)).symm

/-- Extension of scalars along composable maps of commutative ring sheaves is canonically
isomorphic to extension of scalars along a morphism identified with the composite. -/
noncomputable def extendScalarsCompIsoOfEq {O1 O2 O3 : Sheaf J CommRingCat.{max u v}}
    (α : O1 ⟶ O2) (β : O2 ⟶ O3) (γ : O1 ⟶ O3) (hγ : α ≫ β = γ)
    [(restrictScalars (ringSheafMap α)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap β)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap γ)).IsRightAdjoint] :
    extendScalars (ringSheafMap α) ⋙ extendScalars (ringSheafMap β) ≅
      extendScalars (ringSheafMap γ) :=
  Adjunction.leftAdjointUniq
    (((extendRestrictAdjunction (ringSheafMap α)).comp
        (extendRestrictAdjunction (ringSheafMap β))).ofNatIsoRight
      ((restrictionAlongCompIso α β).symm ≪≫
        eqToIso (congrArg (fun t ↦ restrictionAlong t) hγ)))
    (extendRestrictAdjunction (ringSheafMap γ))

/-- `extendScalarsCompIsoOfEq` is uniqueness of left adjoints after transporting the composite
extension-restriction adjunction along `restrictionAlongCompIso`. -/
theorem extendScalarsCompIsoOfEq_eq {O1 O2 O3 : Sheaf J CommRingCat.{max u v}}
    (α : O1 ⟶ O2) (β : O2 ⟶ O3) (γ : O1 ⟶ O3) (hγ : α ≫ β = γ)
    [(restrictScalars (ringSheafMap α)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap β)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap γ)).IsRightAdjoint] :
    extendScalarsCompIsoOfEq α β γ hγ =
      Adjunction.leftAdjointUniq
        (((extendRestrictAdjunction (ringSheafMap α)).comp
            (extendRestrictAdjunction (ringSheafMap β))).ofNatIsoRight
          ((restrictionAlongCompIso α β).symm ≪≫
            eqToIso (congrArg (fun t ↦ restrictionAlong t) hγ)))
        (extendRestrictAdjunction (ringSheafMap γ)) := sorry

/-- Extension of scalars along a section of a ring-sheaf morphism, followed by extension along
that morphism, is isomorphic to the identity functor. -/
noncomputable def extendScalarsSectionIso {O' O : Sheaf J CommRingCat.{max u v}}
    (σ : O ⟶ O') (π : O' ⟶ O) (hσ : σ ≫ π = 𝟙 O)
    [(restrictScalars (ringSheafMap σ)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap π)).IsRightAdjoint] :
    extendScalars (ringSheafMap σ) ⋙ extendScalars (ringSheafMap π) ≅
      𝟭 (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) :=
  Adjunction.leftAdjointUniq
    (((extendRestrictAdjunction (ringSheafMap σ)).comp
        (extendRestrictAdjunction (ringSheafMap π))).ofNatIsoRight
      ((restrictionAlongCompIso σ π).symm ≪≫
        eqToIso (congrArg (fun t ↦ restrictionAlong t) hσ) ≪≫
          (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
            ((sheafCompose J
                (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map_id O)).symm))
    Adjunction.id

/-- `extendScalarsSectionIso` is uniqueness of left adjoints after identifying the composite
restriction functor with the identity via `σ ≫ π = 𝟙`. -/
theorem extendScalarsSectionIso_eq {O' O : Sheaf J CommRingCat.{max u v}}
    (σ : O ⟶ O') (π : O' ⟶ O) (hσ : σ ≫ π = 𝟙 O)
    [(restrictScalars (ringSheafMap σ)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap π)).IsRightAdjoint] :
    extendScalarsSectionIso σ π hσ =
      Adjunction.leftAdjointUniq
        (((extendRestrictAdjunction (ringSheafMap σ)).comp
            (extendRestrictAdjunction (ringSheafMap π))).ofNatIsoRight
          ((restrictionAlongCompIso σ π).symm ≪≫
            eqToIso (congrArg (fun t ↦ restrictionAlong t) hσ) ≪≫
              (SheafOfModules.Restriction.idIso' (ringSheafMap (𝟙 O))
                ((sheafCompose J
                    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map_id O)).symm))
        Adjunction.id := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
