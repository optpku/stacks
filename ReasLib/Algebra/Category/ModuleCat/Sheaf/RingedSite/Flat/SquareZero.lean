/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.SquareZero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness and square-zero reductions of module sheaves

A square-zero reduction consists of a square-zero short exact kernel sequence of structure
sheaves and a right exact module sequence.  Its first map must be induced by the actual ideal
action: after precomposition with `I ⊗ F' ⟶ I ⊗ F`, it is multiplication on `F'`.  Thus `F` is the
actual reduction `F' / I F'`.  Monicity of the action map is a flatness criterion, not an assumption
on reduction data.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O' O : Sheaf J CommRingCat.{max u v}}

namespace SquareZeroReduction

/-- The kernel sequence `I ⟶ O' ⟶ O` associated to a same-site reduction. -/
noncomputable def idealSequence (alpha : O' ⟶ O)
    (I : ringedSiteModuleCategory J O')
    (i : I ⟶ unitModule J O')
    (h : i ≫ SheafOfModules.unitToPushforwardObjUnit
      (ringedSiteStructureMap alpha) = 0) :
    ShortComplex (ringedSiteModuleCategory J O') :=
  ShortComplex.mk i
    (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha)) h

/-- The module sequence `I ⊗ F ⟶ F' ⟶ F` associated to a square-zero reduction. -/
noncomputable def quotientSequence (alpha : O' ⟶ O)
    (I F' : ringedSiteModuleCategory J O')
    (F : ringedSiteModuleCategory J O)
    (tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F')
    (quot : F' ⟶ (restrictionAlong alpha).obj F)
    (h : tensorTo ≫ quot = 0) :
    ShortComplex (ringedSiteModuleCategory J O') :=
  ShortComplex.mk tensorTo quot h

end SquareZeroReduction

/-- A square-zero reduction of a module consists of a square-zero short exact kernel sequence
and a right exact quotient sequence `I ⊗ F ⟶ F' ⟶ F ⟶ 0`, compatible with the actual ideal action.
The compatibility and right exactness identify `F` with `F' / I F'` without assuming that
`I ⊗ F ⟶ F'` is monic. -/
@[stacks 08M4 "reduction data"]
class IsSquareZeroReduction
    (alpha : O' ⟶ O)
    (I : ringedSiteModuleCategory J O')
    (i : I ⟶ unitModule J O')
    (F' : ringedSiteModuleCategory J O')
    (F : ringedSiteModuleCategory J O)
    (tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F')
    (quot : F' ⟶ (restrictionAlong alpha).obj F) : Prop where
  /-- The ideal inclusion followed by the structure map is zero. -/
  ideal_comp :
    i ≫ SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha) = 0
  /-- The kernel sequence `I ⟶ O' ⟶ O` is short exact. -/
  ideal_shortExact :
    (SquareZeroReduction.idealSequence alpha I i ideal_comp).ShortExact
  /-- The ideal inclusion, transported to the tensor unit, is square-zero. -/
  square_zero :
    CategoryTheory.MonoidalCategory.IsSquareZero (i ≫ unitIsoTensorUnit.hom)
  /-- The tensor-action map followed by the quotient map is zero. -/
  quotient_comp : tensorTo ≫ quot = 0
  /-- The module reduction sequence `I ⊗ F ⟶ F' ⟶ F ⟶ 0` is right exact. -/
  quotient_rightExact :
    (SquareZeroReduction.quotientSequence alpha I F' F tensorTo quot quotient_comp).Exact ∧
      Epi quot
  /-- The first map is induced by multiplication by the ideal, using the given quotient map. -/
  action_comp :
    moduleTensorMap (𝟙 I) quot ≫ tensorTo =
      moduleTensorMap (i ≫ unitIsoTensorUnit.hom) (𝟙 F') ≫ (λ_ F').hom

namespace IsSquareZeroReduction

variable {alpha : O' ⟶ O}
variable {I : ringedSiteModuleCategory J O'} {i : I ⟶ unitModule J O'}
variable {F' : ringedSiteModuleCategory J O'} {F : ringedSiteModuleCategory J O}
variable {tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F'}
variable {quot : F' ⟶ (restrictionAlong alpha).obj F}

/-- The ideal inclusion in a square-zero reduction is a monomorphism. -/
theorem idealInclusion_mono
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) : Mono i :=
  h.ideal_shortExact.mono_f

/-- The structure-map quotient in a square-zero reduction is an epimorphism. -/
theorem structureMap_epi
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) :
    Epi (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha)) :=
  h.ideal_shortExact.epi_g

/-- The module quotient map in a square-zero reduction is an epimorphism. -/
theorem quotient_epi
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) : Epi quot :=
  h.quotient_rightExact.2

/-- The ideal part of a square-zero reduction consists simultaneously of a short exact kernel
sequence and the sectionwise square-zero condition. -/
theorem ideal_spec [h : IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    (SquareZeroReduction.idealSequence alpha I i h.ideal_comp).ShortExact ∧
      CategoryTheory.MonoidalCategory.IsSquareZero
        (i ≫ unitIsoTensorUnit.hom) :=
  ⟨h.ideal_shortExact, h.square_zero⟩

/-- The quotient part of a square-zero reduction is a right exact module sequence. -/
theorem quotient_spec [h : IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    (SquareZeroReduction.quotientSequence
      alpha I F' F tensorTo quot h.quotient_comp).Exact ∧ Epi quot :=
  h.quotient_rightExact

/-- Lemma 18.28.15 (08M4): a module over a square-zero thickening is flat exactly when its
reduction is flat and the kernel-action map is monic. -/
@[stacks 08M4]
theorem isFlat_iff [IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    IsFlat O' F' ↔ IsFlat O F ∧ Mono tensorTo := sorry

end IsSquareZeroReduction

end SheafOfModules.RingedSite
