/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import ReasLib.Algebra.Module.ULift
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued shifted Hom along an adjunction

The pointwise adjunction equivalence is assembled into target-functor isomorphisms.  The direct
version is for a common Hom universe; the general version uses the canonical asymmetric lifts
that place both functors in `ModuleCat.{max vC vD} R`.
-/

@[expose] public section

noncomputable section

universe uR vC uC vD uD

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {R : Type uR} [Ring R]

section SameUniverse

universe v uC' uD'

variable {C : Type uC'} {D : Type uD'}
variable [Category.{v} C] [Category.{v} D]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- In a common Hom universe, the pointwise comparison assembles into an isomorphism of
module-valued target functors. -/
@[reassoc, stacks 09LN "naturality of the same-universe shifted-Hom target comparison"]
theorem targetFunctorIso_naturality (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) {Y Y' : D} (h : Y ⟶ Y') :
    (G ⋙ ShiftedHom.targetFunctor R X n).map h ≫
        (adj.shiftedHomLinearEquiv (R := R) X Y' n).toModuleIso.hom =
      (adj.shiftedHomLinearEquiv (R := R) X Y n).toModuleIso.hom ≫
        (ShiftedHom.targetFunctor R (F.obj X) n).map h := sorry

/-- In a common Hom universe, the pointwise comparison assembles into an isomorphism of
module-valued target functors. -/
@[stacks 09LN "same-universe shifted-Hom target-functor isomorphism"]
noncomputable def targetFunctorIso (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) :
    G ⋙ ShiftedHom.targetFunctor R X n ≅
      ShiftedHom.targetFunctor R (F.obj X) n :=
  NatIso.ofComponents
    (fun Y ↦ (adj.shiftedHomLinearEquiv (R := R) X Y n).toModuleIso)
    (fun h ↦ targetFunctorIso_naturality adj X n h)

/-- The component of the same-universe shifted-Hom target isomorphism is the pointwise linear
equivalence. -/
@[simp, stacks 09LN "component of the same-universe shifted-Hom target isomorphism"]
theorem targetFunctorIso_app (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) (Y : D) :
    (adj.targetFunctorIso X n).app Y =
      (adj.shiftedHomLinearEquiv (R := R) X Y n).toModuleIso := sorry

end SameUniverse

section MixedUniverse

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- Asymmetric universe lifts place the shifted-adjunction comparison in one common
`ModuleCat` universe when the two categories have different Hom universes. -/
@[reassoc, stacks 09LN "naturality of the universe-lifted shifted-Hom target comparison"]
theorem uliftTargetFunctorIso_naturality (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) {Y Y' : D} (h : Y ⟶ Y') :
    ((G ⋙ ShiftedHom.targetFunctor R X n) ⋙ ModuleCat.uliftFunctor.{vD} R).map h ≫
        (LinearEquiv.ulift
          (adj.shiftedHomLinearEquiv (R := R) X Y' n)).toModuleIso.hom =
      (LinearEquiv.ulift
          (adj.shiftedHomLinearEquiv (R := R) X Y n)).toModuleIso.hom ≫
        ((ShiftedHom.targetFunctor R (F.obj X) n) ⋙
          ModuleCat.uliftFunctor.{vC} R).map h := sorry

/-- The shifted-Hom adjunction as a target-functor isomorphism across different Hom universes.
The `G` and `F` sides use the opposite Hom universe as their `ULift` level, so both land in
`ModuleCat.{max vC vD} R`. -/
@[stacks 09LN "universe-lifted shifted-Hom target-functor isomorphism",
  stacks 0CS5 "promoted universe-lifted shifted-Hom adjunction bridge"]
noncomputable def uliftTargetFunctorIso (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) :
    (G ⋙ ShiftedHom.targetFunctor R X n) ⋙
        ModuleCat.uliftFunctor.{vD} R ≅
      (ShiftedHom.targetFunctor R (F.obj X) n) ⋙
        ModuleCat.uliftFunctor.{vC} R :=
  NatIso.ofComponents
    (fun Y ↦
      (LinearEquiv.ulift
        (adj.shiftedHomLinearEquiv (R := R) X Y n)).toModuleIso)
    (fun h ↦ uliftTargetFunctorIso_naturality adj X n h)

/-- The component of the universe-lifted target isomorphism is the asymmetric-`ULift` pointwise
linear equivalence. -/
@[simp, stacks 09LN "component of the universe-lifted shifted-Hom target isomorphism",
  stacks 0CS5 "component of the promoted shifted-Hom adjunction bridge"]
theorem uliftTargetFunctorIso_app (adj : F ⊣ G) [G.CommShift ℤ]
    [F.Additive] [F.Linear R] (X : C) (n : ℤ) (Y : D) :
    (adj.uliftTargetFunctorIso X n).app Y =
      (LinearEquiv.ulift
        (adj.shiftedHomLinearEquiv (R := R) X Y n)).toModuleIso := sorry

end MixedUniverse

end CategoryTheory.Adjunction
