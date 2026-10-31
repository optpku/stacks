/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Closure properties of finite locally constant sheaves

This module owns the reusable closure API for finite locally constant sheaves.
The statements are organized by the object property they concern, so clients
can use the finite-limit, finite-colimit, kernel, cokernel, and weak-Serre facts
without importing a textbook chapter.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u v w u₁

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

namespace finiteLocallyConstant

/-- The finite locally constant set-valued object property is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms :
    (finiteLocallyConstant J).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hF := by
    letI : IsFiniteLocallyConstant X := hF
    refine ⟨?_⟩
    intro U
    obtain ⟨I, U', hU', hchart⟩ :=
      IsLocallyConstantWith.existsConstantCover (P := Finite) (F := X) U
    refine ⟨I, U', hU', ?_⟩
    intro i
    obtain ⟨E, hE, ⟨e_i⟩⟩ := hchart i
    refine ⟨E, hE, ⟨((J.overPullback (Type w) (U' i).left).mapIso e).symm ≪≫ e_i⟩⟩

/-- Finite locally constant set-valued sheaves are closed
under limits indexed by a finite category. -/
@[stacks 093U "(1), finite limits"]
instance isClosedUnderLimitsOfShape (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape (finiteLocallyConstant J) K := sorry

/-- Finite locally constant set-valued sheaves are closed
under colimits indexed by a finite category. -/
@[stacks 093U "(1), finite colimits"]
instance isClosedUnderColimitsOfShape (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape (finiteLocallyConstant J) K := sorry

end finiteLocallyConstant

end Types

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [Abelian (Sheaf J AddCommGrpCat.{w})]

namespace IsFiniteLocallyConstantAddCommGrp

/-- Kernels of maps between finite locally constant abelian sheaves are finite locally
constant. -/
theorem kernel {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsFiniteLocallyConstantAddCommGrp G] :
    IsFiniteLocallyConstantAddCommGrp (Limits.kernel f) := sorry

/-- Cokernels of maps between finite locally constant abelian sheaves are finite locally
constant. -/
theorem cokernel {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsFiniteLocallyConstantAddCommGrp G] :
    IsFiniteLocallyConstantAddCommGrp (Limits.cokernel f) := sorry

end IsFiniteLocallyConstantAddCommGrp

namespace finiteLocallyConstantAddCommGrp

/-- Finite locally constant abelian sheaves form a weak Serre class. -/
@[stacks 093U "(2)"]
instance isWeakSerreClass :
    IsWeakSerreClass (finiteLocallyConstantAddCommGrp J) := sorry

end finiteLocallyConstantAddCommGrp

end AddCommGroups

section Modules

variable {R : Type w} [Ring R] [IsNoetherianRing R]
variable [HasWeakSheafify J (ModuleCat.{w} R)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
variable [Abelian (Sheaf J (ModuleCat.{w} R))]

namespace IsFiniteTypeLocallyConstantModule

/-- Over a Noetherian ring, kernels of maps between finite-type locally constant module sheaves
remain finite-type locally constant. -/
theorem kernel {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsFiniteTypeLocallyConstantModule G] :
    IsFiniteTypeLocallyConstantModule (Limits.kernel f) := sorry

/-- Cokernels of maps between finite-type locally constant module sheaves remain finite-type
locally constant. -/
theorem cokernel {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsFiniteTypeLocallyConstantModule G] :
    IsFiniteTypeLocallyConstantModule (Limits.cokernel f) := sorry

end IsFiniteTypeLocallyConstantModule

namespace finiteTypeLocallyConstantModule

/-- Over a Noetherian ring, finite-type locally constant module sheaves form
a weak Serre class. -/
@[stacks 093U "(3)"]
instance isWeakSerreClass :
    IsWeakSerreClass (finiteTypeLocallyConstantModule J R) := sorry

end finiteTypeLocallyConstantModule

end Modules

end CategoryTheory.Sheaf
