/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Pullback.SiteSized

/-!
# Sheaves of modules with site-sized section carriers
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace SheafOfModules.SiteSized

/-- The abelian structure on module sheaves obtained from the plus-construction
sheafification at the size of the site. -/
@[reducible]
def abelian {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) :
    Abelian (SheafOfModules.{max u v} R) := by
  -- Local instance justification (instance diamond): fix the proved plus-construction certificate used by the abelian transfer.
  letI : HasSheafify J AddCommGrpCat.{max u v} := inferInstance
  -- Local instance justification (instance diamond): use the matching plus-construction locally-bijective criterion.
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
  infer_instance

/-- Pushforward along a continuous coefficient morphism has a left adjoint,
constructed by presheaf extension followed by sheafification. -/
instance pushforwardIsRightAdjoint {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{max u v}} {R : Sheaf K RingCat.{max u v}}
    [F.IsContinuous J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} J K).obj R) :
    (SheafOfModules.pushforward.{max u v} φ).IsRightAdjoint := by
  -- Local instance justification (instance diamond): select the explicit site-sized presheaf extension adjunction.
  letI := PresheafOfModules.SiteSized.pushforwardIsRightAdjoint φ.hom
  -- Local instance justification (instance diamond): fix the proved plus-construction weak sheafification for this adjunction.
  letI : HasWeakSheafify K AddCommGrpCat.{max u v} :=
    (inferInstance : HasSheafify K AddCommGrpCat.{max u v}).isRightAdjoint
  -- Local instance justification (instance diamond): use the locally-bijective criterion of the same plus construction.
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
  exact (SheafOfModules.PullbackConstruction.adjunction φ).isRightAdjoint

end SheafOfModules.SiteSized

namespace PresheafOfModules.SiteSized

/-- Sheafification of module presheaves over a fixed ring sheaf, using the
plus construction at the size of the site. -/
def sheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) :
    PresheafOfModules.{max u v} R.obj ⥤ SheafOfModules.{max u v} R := by
  -- Local instance justification (instance diamond): fix the proved plus-construction weak sheafification for the module functor.
  letI : HasWeakSheafify J AddCommGrpCat.{max u v} :=
    (inferInstance : HasSheafify J AddCommGrpCat.{max u v}).isRightAdjoint
  -- Local instance justification (instance diamond): use the matching plus-construction locally-bijective criterion.
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
  exact PresheafOfModules.sheafification (R := R) (𝟙 R.obj)

end PresheafOfModules.SiteSized
