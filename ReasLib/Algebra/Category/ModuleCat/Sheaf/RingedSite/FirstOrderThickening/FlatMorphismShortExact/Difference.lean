/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction.Composition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift.IsoClass
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Trivialization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension.Pushout
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction

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

/-- The `O'_1`-module `π* F` obtained by extending scalars of `restrictModule S` along the
canonical splitting of the top row. -/
noncomputable def canonicalPullback
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J O1' :=
  (extendScalars (ringSheafMap (canonicalTrivialization S))).obj (restrictModule S)

/-- `canonicalPullback` is extension of scalars of `restrictModule` along the canonical
splitting. -/
theorem canonicalPullback_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    canonicalPullback S =
      (extendScalars (ringSheafMap (canonicalTrivialization S))).obj
        (restrictModule S) := sorry

/-- The comparison `i* (π* F) ≅ F` induced by `σ ≫ π1 = 𝟙`. -/
noncomputable def canonicalPullbackRestrictIso
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    (extendScalars (ringSheafMap π1)).obj (canonicalPullback S) ≅ restrictModule S :=
  (extendScalarsSectionIso (canonicalTrivialization S) π1
      (canonicalTrivialization_isTrivialization S.h S.g
        (isShortExact_isComplex S.h S.g S.ses_top))).app (restrictModule S)

/-- `canonicalPullbackRestrictIso` is the section-iso of extension of scalars on
`restrictModule`. -/
theorem canonicalPullbackRestrictIso_eq
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    canonicalPullbackRestrictIso S =
      (extendScalarsSectionIso (canonicalTrivialization S) π1
          (canonicalTrivialization_isTrivialization S.h S.g
            (isShortExact_isComplex S.h S.g S.ses_top))).app
        (restrictModule S) := sorry

/-- The `O'_1`-module `h* F'_2` obtained by extending scalars of the stored middle module along
`h`. -/
noncomputable def homPullback (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J O1' :=
  (extendScalars (ringSheafMap S.h.hom)).obj S.module

/-- `homPullback` is extension of scalars of the stored `O'_2`-module along `h`. -/
theorem homPullback_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullback S = (extendScalars (ringSheafMap S.h.hom)).obj S.module := sorry

/-- The comparison `i* (h* F'_2) ≅ F` induced by `h.hom ≫ π1 = π2`. -/
noncomputable def homPullbackRestrictIso
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (extendScalars (ringSheafMap π1)).obj (homPullback S) ≅ restrictModule S :=
  (extendScalarsCompIsoOfEq S.h.hom π1 π2 S.h.comm).app S.module

/-- `homPullbackRestrictIso` is `extendScalarsCompIsoOfEq` on the stored middle module. -/
theorem homPullbackRestrictIso_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullbackRestrictIso S =
      (extendScalarsCompIsoOfEq S.h.hom π1 π2 S.h.comm).app S.module := sorry

/-- `π* F` is flat over `O_{B'_1}`. -/
theorem canonicalPullback_isFlat
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    IsFlat OB1' ((restrictionAlong S.f1').obj (canonicalPullback S)) := sorry

/-- `h* F'_2` is flat over `O_{B'_1}`. -/
theorem homPullback_isFlat (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    IsFlat OB1' ((restrictionAlong S.f1').obj (homPullback S)) := sorry

/-- The flat lift of `F` along `π1` whose middle module is `π* F`. -/
noncomputable def canonicalLift (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    FlatLift π1 S.f1' (restrictModule S) :=
  FlatLift.of π1 S.f1' (restrictModule S) (canonicalPullback S)
    (canonicalPullbackRestrictIso S) (canonicalPullback_isFlat S)

/-- The middle module of `canonicalLift` is `canonicalPullback`. -/
theorem canonicalLift_module (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    (canonicalLift S).module = canonicalPullback S := sorry

/-- The flat lift of `F` along `π1` whose middle module is `h* F'_2`. -/
noncomputable def homLift (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    FlatLift π1 S.f1' (restrictModule S) :=
  FlatLift.of π1 S.f1' (restrictModule S) (homPullback S)
    (homPullbackRestrictIso S) (homPullback_isFlat S)

/-- The middle module of `homLift` is `homPullback`. -/
theorem homLift_module (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (homLift S).module = homPullback S := sorry

/-- The stored middle module, with its definitional restriction isomorphism, as a flat lift
along `π2`. -/
noncomputable def middleLift (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    FlatLift π2 S.f2' (restrictModule S) :=
  FlatLift.of π2 S.f2' (restrictModule S) S.module (Iso.refl _)
    S.module_isFlatOver

/-- The middle module of `middleLift` is the stored `O'_2`-module. -/
theorem middleLift_module (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (middleLift S).module = S.module := sorry

/-- `F = F'_2 ⊗ O` is flat over `O_B`. -/
theorem restrictModule_isFlat (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsFlat O_B ((restrictionAlong f).obj (restrictModule S)) := sorry

/-- Strictness of `(f, f'_1)` together with flatness of `f'_1` identifies `I_1` with
`f^* J_1`. -/
theorem idealMap_fst_isIso (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso S.idealMap_fst := sorry

/-- Strictness of `(f, f'_2)` together with flatness of `f'_2` identifies `I_2` with
`f^* J_2`. -/
theorem idealMap_snd_isIso (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso S.idealMap_snd := sorry

/-- Strictness of `(f, f'_3)` together with flatness of `f'_3` identifies `I_3` with
`f^* J_3`. -/
theorem idealMap_thd_isIso (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso S.idealMap_thd := sorry

/-- Tensoring the first-column kernel-pullback comparison with `F` is an isomorphism. -/
theorem moduleTensor_idealMap_fst_isIso
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso (moduleTensorMap S.idealMap_fst (𝟙 (restrictModule S))) := sorry

/-- Tensoring the middle-column kernel-pullback comparison with `F` is an isomorphism. -/
theorem moduleTensor_idealMap_snd_isIso
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso (moduleTensorMap S.idealMap_snd (𝟙 (restrictModule S))) := sorry

/-- Tensoring the last-column kernel-pullback comparison with `F` is an isomorphism. -/
theorem moduleTensor_idealMap_thd_isIso
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsIso (moduleTensorMap S.idealMap_thd (𝟙 (restrictModule S))) := sorry

/-- The infinitesimal comparison `c_1 : I_1 ⊗ F ⟶ f^* J_1 ⊗ F` inverse to the first-column
kernel-tensor map. -/
noncomputable def infMap_fst (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    moduleTensor (ideal π1) (restrictModule S) ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1))
        (restrictModule S) :=
  @inv _ _ _ _ (moduleTensorMap S.idealMap_fst (𝟙 (restrictModule S)))
    (moduleTensor_idealMap_fst_isIso S)

/-- `infMap_fst` is the inverse of the first-column kernel-tensor comparison. -/
theorem infMap_fst_spec (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    infMap_fst S =
      @inv _ _ _ _ (moduleTensorMap S.idealMap_fst (𝟙 (restrictModule S)))
        (moduleTensor_idealMap_fst_isIso S) := sorry

/-- The infinitesimal comparison `c_2 : I_2 ⊗ F ⟶ f^* J_2 ⊗ F`. -/
noncomputable def infMap_snd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    moduleTensor (ideal π2) (restrictModule S) ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2))
        (restrictModule S) :=
  @inv _ _ _ _ (moduleTensorMap S.idealMap_snd (𝟙 (restrictModule S)))
    (moduleTensor_idealMap_snd_isIso S)

/-- `infMap_snd` is the inverse of the middle-column kernel-tensor comparison. -/
theorem infMap_snd_spec (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    infMap_snd S =
      @inv _ _ _ _ (moduleTensorMap S.idealMap_snd (𝟙 (restrictModule S)))
        (moduleTensor_idealMap_snd_isIso S) := sorry

/-- The infinitesimal comparison `c_3 : I_3 ⊗ F ⟶ f^* J_3 ⊗ F`. -/
noncomputable def infMap_thd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    moduleTensor (ideal π3) (restrictModule S) ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ3))
        (restrictModule S) :=
  @inv _ _ _ _ (moduleTensorMap S.idealMap_thd (𝟙 (restrictModule S)))
    (moduleTensor_idealMap_thd_isIso S)

/-- `infMap_thd` is the inverse of the last-column kernel-tensor comparison. -/
theorem infMap_thd_spec (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    infMap_thd S =
      @inv _ _ _ _ (moduleTensorMap S.idealMap_thd (𝟙 (restrictModule S)))
        (moduleTensor_idealMap_thd_isIso S) := sorry

/-- The coefficient map `f^* J_2 ⊗ F ⟶ f^* J_1 ⊗ F` induced by the base thickening. -/
noncomputable def coeffMap_snd_fst (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2)) (restrictModule S) ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1))
        (restrictModule S) :=
  moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base.idealMap)
    (𝟙 (restrictModule S))

/-- `coeffMap_snd_fst` is the tensor morphism of `f^*` of the first base ideal map. -/
theorem coeffMap_snd_fst_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    coeffMap_snd_fst S =
      moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base.idealMap)
        (𝟙 (restrictModule S)) := sorry

/-- The coefficient map `f^* J_3 ⊗ F ⟶ f^* J_2 ⊗ F` induced by the second base thickening. -/
noncomputable def coeffMap_thd_snd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ3)) (restrictModule S) ⟶
      moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2))
        (restrictModule S) :=
  moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base'.idealMap)
    (𝟙 (restrictModule S))

/-- `coeffMap_thd_snd` is the tensor morphism of `f^*` of the second base ideal map. -/
theorem coeffMap_thd_snd_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    coeffMap_thd_snd S =
      moduleTensorMap ((extendScalars (ringSheafMap f)).map S.base'.idealMap)
        (𝟙 (restrictModule S)) := sorry

/-- The two coefficient maps compose to zero. -/
theorem coeff_comp (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    coeffMap_thd_snd S ≫ coeffMap_snd_fst S = 0 := sorry

/-- The coefficient short complex `f^* J_3 ⊗ F ⟶ f^* J_2 ⊗ F ⟶ f^* J_1 ⊗ F`. -/
noncomputable def coeffShortComplex (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) :=
  ShortComplex.mk (coeffMap_thd_snd S) (coeffMap_snd_fst S) (coeff_comp S)

/-- `coeffShortComplex` is the two-step complex of pullback ideal tensors. -/
theorem coeffShortComplex_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    coeffShortComplex S =
      ShortComplex.mk (coeffMap_thd_snd S) (coeffMap_snd_fst S) (coeff_comp S) := sorry

/-- The sequence `0 → f^* J_3 ⊗ F → f^* J_2 ⊗ F → f^* J_1 ⊗ F → 0` is short exact. -/
theorem coeff_shortExact (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (coeffShortComplex S).ShortExact := sorry

/-- The infinitesimal maps `c_2`, `h.idealMap ⊗ 𝟙`, `coeffMap_snd_fst`, and `c_1` form a
commutative square. -/
theorem infMap_comm_fst (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq (infMap_snd S)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget S.h.hom S.h.comm hπ1.isSquareZero hπ2.isSquareZero)
        (𝟙 (restrictModule S)))
      (coeffMap_snd_fst S) (infMap_fst S) := sorry

/-- The infinitesimal maps `c_3`, `g.idealMap ⊗ 𝟙`, `coeffMap_thd_snd`, and `c_2` form a
commutative square. -/
theorem infMap_comm_snd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq (infMap_thd S)
      (moduleTensorMap (KernelIdeal.IsSquareZero.mapToTarget S.g.hom S.g.comm hπ2.isSquareZero hπ3.isSquareZero)
        (𝟙 (restrictModule S)))
      (coeffMap_thd_snd S) (infMap_snd S) := sorry

/-- The transported kernel inclusion into the stored middle module. -/
noncomputable def middleIncl (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (restrictionAlong π2).obj
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2)) (restrictModule S)) ⟶
      S.module :=
  (restrictionAlong π2).map
    (moduleTensorMap S.idealMap_snd (𝟙 (restrictModule S)) ≫
      FlatLift.transportedInfMap (middleLift S)) ≫ (ofPullback π2 S.module).ι

/-- The adjunct projection from the stored middle module to its reduction. -/
noncomputable def middleProj (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    S.module ⟶ (restrictionAlong π2).obj (restrictModule S) :=
  extendRestrictHomEquiv (ringSheafMap π2) S.module (restrictModule S) (middleLift S).isoHom

/-- The stored middle inclusion and projection compose to zero. -/
theorem middleExtension_zero (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    middleIncl S ≫ middleProj S = 0 := sorry

/-- The stored middle maps form a short exact sequence. -/
theorem middleExtension_shortExact (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (ShortComplex.mk (middleIncl S) (middleProj S) (middleExtension_zero S)).ShortExact := sorry

/-- The middle sequence has the infinitesimal action prescribed by the ideal comparison. -/
theorem middleExtension_compatible (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CompatibleC hπ2.isSquareZero (middleIncl S) (middleProj S) (infMap_snd S) := sorry

/-- The extension of `F` by `f^* J_2 ⊗ F` with infinitesimal map `c_2` whose middle
module is the stored `F'_2`. -/
noncomputable def middleExtension (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    ModuleExtension hπ2.isSquareZero (restrictModule S)
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ2)) (restrictModule S))
      (infMap_snd S) :=
  ModuleExtension.of S.module (middleIncl S) (middleProj S)
    (middleExtension_zero S) (middleExtension_shortExact S) (middleExtension_compatible S)

/-- The middle module of `middleExtension` is the stored `O'_2`-module. -/
theorem middleExtension_module (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (middleExtension S).module = S.module := sorry

/-- The pushout of `middleExtension` along `h`, as an extension of `F` by
`f^* J_1 ⊗ F` on the first thickening. -/
noncomputable def homExtension (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    ModuleExtension hπ1.isSquareZero (restrictModule S)
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1)) (restrictModule S))
      (infMap_fst S) :=
  ModuleExtension.pushout S.h.hom S.h.comm (coeffMap_snd_fst S) (infMap_comm_fst S)
    (middleExtension S)

/-- The middle sheaf of `homExtension` is the abelian pushout of `F'_2` along
`coeffMap_snd_fst`. -/
theorem homExtension_module_eq_pushoutSheaf
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (homExtension S).module =
      ModuleExtension.pushoutSheaf S.h.hom S.h.comm (coeffMap_snd_fst S)
        (infMap_comm_fst S) (middleExtension S) := sorry

/-- The transported kernel inclusion into extension of scalars along the first diagram map. -/
noncomputable def homPullbackIncl (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (restrictionAlong π1).obj
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1)) (restrictModule S)) ⟶
      homPullback S :=
  (restrictionAlong π1).map
    (moduleTensorMap S.idealMap_fst (𝟙 (restrictModule S)) ≫
      FlatLift.transportedInfMap (homLift S)) ≫ (ofPullback π1 (homPullback S)).ι

/-- The middle-term leg of the additive pushout is linear over the source ring. -/
theorem homExtensionUnit_smul (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    (U : Cᵒᵖ) (r : (ringSheaf J O2').obj.obj U) (m : S.module.val.obj U) :
    (Extension.pushoutInlSheaf (middleExtension S).toExtension (coeffMap_snd_fst S)).hom.app U
        ((S.module.val.obj U).isModule.smul r m) =
      (((restrictionAlong S.h.hom).obj (homExtension S).module).val.obj U).isModule.smul r
        ((Extension.pushoutInlSheaf (middleExtension S).toExtension
          (coeffMap_snd_fst S)).hom.app U m) := sorry

/-- The source-linear middle-term leg into the changed-scalar pushout. -/
noncomputable def homExtensionUnit (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    S.module ⟶ (restrictionAlong S.h.hom).obj (homExtension S).module where
  val := PresheafOfModules.homMk
    (Extension.pushoutInlSheaf (middleExtension S).toExtension (coeffMap_snd_fst S)).hom
    (homExtensionUnit_smul S)

/-- The adjoint of the pushout middle-term leg compares scalar extension with pushout. -/
noncomputable def homPullbackToPushout (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullback S ⟶ (homExtension S).module :=
  (extendRestrictHomEquiv (ringSheafMap S.h.hom) S.module (homExtension S).module).symm
    (homExtensionUnit S)

/-- The adjunction unit and transported kernel inclusion agree on the pushout relation. -/
theorem pushoutToHomPullback_comm (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    Extension.inclUnderlying (middleExtension S).toExtension ≫
        (SheafOfModules.toSheaf (ringSheaf J O2')).map
          ((extendRestrictAdjunction (ringSheafMap S.h.hom)).unit.app S.module) =
      Extension.kernelUnderlying (coeffMap_snd_fst S) ≫
        (SheafOfModules.toSheaf (ringSheaf J O1')).map (homPullbackIncl S) := sorry

/-- The additive-pushout descent of the adjunction unit and transported kernel inclusion. -/
noncomputable def pushoutToHomPullbackUnderlying (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    Extension.pushoutUnderlying (middleExtension S).toExtension (coeffMap_snd_fst S) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O1')).obj (homPullback S) :=
  Limits.pushout.desc
    ((SheafOfModules.toSheaf (ringSheaf J O2')).map
      ((extendRestrictAdjunction (ringSheafMap S.h.hom)).unit.app S.module))
    ((SheafOfModules.toSheaf (ringSheaf J O1')).map (homPullbackIncl S))
    (pushoutToHomPullback_comm S)

/-- The additive comparison from pushout to scalar extension is linear over the target ring. -/
theorem pushoutToHomPullback_smul (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint]
    (U : Cᵒᵖ) (r : (ringSheaf J O1').obj.obj U)
    (m : (homExtension S).module.val.obj U) :
    (pushoutToHomPullbackUnderlying S).hom.app U
        (((homExtension S).module.val.obj U).isModule.smul r m) =
      ((homPullback S).val.obj U).isModule.smul r
        ((pushoutToHomPullbackUnderlying S).hom.app U m) := sorry

/-- The linear comparison from the changed-scalar pushout to scalar extension. -/
noncomputable def pushoutToHomPullback (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (homExtension S).module ⟶ homPullback S where
  val := PresheafOfModules.homMk (pushoutToHomPullbackUnderlying S).hom
    (pushoutToHomPullback_smul S)

/-- The forward comparison followed by the pushout descent is the identity. -/
theorem homPullbackIsoPushout_hom_inv_id (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullbackToPushout S ≫ pushoutToHomPullback S = 𝟙 (homPullback S) := sorry

/-- The pushout descent followed by the forward comparison is the identity. -/
theorem homPullbackIsoPushout_inv_hom_id (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    pushoutToHomPullback S ≫ homPullbackToPushout S = 𝟙 (homExtension S).module := sorry

/-- Scalar extension along the diagram map is canonically isomorphic to its changed-scalar pushout. -/
noncomputable def homPullbackIsoPushout (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullback S ≅ (homExtension S).module where
  hom := homPullbackToPushout S
  inv := pushoutToHomPullback S
  hom_inv_id := homPullbackIsoPushout_hom_inv_id S
  inv_hom_id := homPullbackIsoPushout_inv_hom_id S

/-- The scalar-extension comparison preserves the transported kernel inclusion. -/
theorem homPullbackIsoPushout_incl (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    homPullbackIncl S ≫ (homPullbackIsoPushout S).hom = (homExtension S).incl := sorry

/-- The scalar-extension comparison preserves the adjunct quotient projection. -/
theorem homPullbackIsoPushout_proj (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (homPullbackIsoPushout S).hom ≫ (homExtension S).proj =
      extendRestrictHomEquiv (ringSheafMap π1) (homPullback S) (restrictModule S)
        (homPullbackRestrictIso S).hom := sorry

/-- The forward comparison is adjoint to the actual pushout middle-term leg. -/
theorem homPullbackIsoPushout_unit (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    (extendRestrictAdjunction (ringSheafMap S.h.hom)).unit.app S.module ≫
        (restrictionAlong S.h.hom).map (homPullbackIsoPushout S).hom =
      homExtensionUnit S := sorry

/-- The difference class `θ` of `π* F` and `h* F'_2` in
`Ext F (f^* J_1 ⊗ F) 1`. -/
noncomputable def difference (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    Ext (restrictModule S)
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ1)) (restrictModule S))
      1 :=
  ModuleExtension.extClass π1 (canonicalTrivialization S)
    (canonicalTrivialization_isTrivialization S.h S.g
      (isShortExact_isComplex S.h S.g S.ses_top))
    (Quotient.mk (ModuleExtension.isomorphicSetoid (infMap_fst S)) (homExtension S))

/-- `difference` is the Ext class of `homExtension` along the canonical splitting. -/
theorem difference_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    difference S =
      ModuleExtension.extClass π1 (canonicalTrivialization S)
        (canonicalTrivialization_isTrivialization S.h S.g
          (isShortExact_isComplex S.h S.g S.ses_top))
        (Quotient.mk (ModuleExtension.isomorphicSetoid (infMap_fst S))
          (homExtension S)) := sorry

/-- The existence obstruction to a flat `O'_3`-lift of `F`. -/
noncomputable def obstruction3 (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O3')] :
    Ext (restrictModule S)
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ3)) (restrictModule S))
      2 :=
  ModuleExtension.existenceObstruction π3 (restrictModule S)
    (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ3)) (restrictModule S))
    (infMap_thd S)

/-- `obstruction3` is the existence obstruction with coefficients `f^* J_3 ⊗ F` and
infinitesimal map `c_3`. -/
theorem obstruction3_eq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O3')] :
    obstruction3 S =
      ModuleExtension.existenceObstruction π3 (restrictModule S)
        (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ3))
          (restrictModule S))
        (infMap_thd S) := sorry

/-- The torsor action of the `I_1 ⊗ F` class corresponding to `difference`
sends the isomorphism class of `canonicalLift` to that of `homLift`. -/
theorem difference_vadd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint]
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint]
    [IsFlat O_B ((restrictionAlong f).obj (restrictModule S))]
    (ξ : ExtensionClass (moduleTensor (ideal π1) (restrictModule S)) (restrictModule S))
    (hξ : ExtensionClass.toExt ξ =
      (Ext.mk₀ (moduleTensorMap S.idealMap_fst (𝟙 (restrictModule S)))).postcomp
        (restrictModule S) (add_zero 1) (difference S)) :
    FlatLift.vadd S.strict1 ξ
        (FlatLift.IsoClass.mk π1 S.f1' (restrictModule S) (canonicalLift S)) =
      FlatLift.IsoClass.mk π1 S.f1' (restrictModule S) (homLift S) := sorry


/-- The canonical scalar extension is relatively flat and has invertible reduction comparison. -/
theorem canonicalPullback_restrict_isFlat
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap (canonicalTrivialization S))).IsRightAdjoint] :
    IsFlat OB1' ((restrictionAlong S.f1').obj (canonicalPullback S)) ∧
      IsIso (canonicalPullbackRestrictIso S).hom := sorry

/-- Scalar extension along the diagram map is relatively flat and has invertible reduction comparison. -/
theorem homPullback_restrict_isFlat
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [(restrictScalars (ringSheafMap S.h.hom)).IsRightAdjoint] :
    IsFlat OB1' ((restrictionAlong S.f1').obj (homPullback S)) ∧
      IsIso (homPullbackRestrictIso S).hom := sorry

/-- The connecting image of the difference class is the existence obstruction on the third thickening. -/
theorem difference_comp_eq_obstruction
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3)
    [HasFunctorialInjectives
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
    [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O3')] :
    (difference S).comp (coeff_shortExact S).extClass (rfl : 1 + 1 = 2) =
      obstruction3 S := sorry

end FlatMorphismShortExact

end SheafOfModules.RingedSite.FirstOrderThickening
