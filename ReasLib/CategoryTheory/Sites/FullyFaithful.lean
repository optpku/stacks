/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fully faithful functors of sites

This file owns the unit and counit isomorphisms on sheaf categories induced by
a fully faithful functor that is both continuous and cocontinuous.  The
bundled statements accept local full-faithfulness evidence directly; companion
instances serve ordinary typeclass-driven applications.
-/

@[expose] public section

open CategoryTheory

universe w vC vD uC uD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)
variable {A : Type w} [Category A]

namespace FullyFaithful

/-- A fully faithful continuous and cocontinuous functor of sites induces an
invertible unit for the continuous sheaf adjunction. -/
@[stacks 077I "(1)"]
theorem sheafAdjunctionContinuous_unit_app_isIso
    (hu : u.FullyFaithful)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    (F : Sheaf J A) [u.op.HasPointwiseLeftKanExtension F.obj]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso ((u.sheafAdjunctionContinuous A J K).unit.app F) := sorry

/-- A fully faithful continuous and cocontinuous functor of sites induces an
invertible counit for the cocontinuous sheaf adjunction. -/
@[stacks 077I "(2)"]
theorem sheafAdjunctionCocontinuous_counit_app_isIso
    (hu : u.FullyFaithful)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf J A) :
    IsIso ((u.sheafAdjunctionCocontinuous A J K).counit.app F) := sorry

/-- A fully faithful continuous and cocontinuous functor of sites has an
invertible unit for its continuous sheaf adjunction.  This bundled form is
suited to applications where full faithfulness is available as local evidence
rather than as ambient instances. -/
theorem sheafAdjunctionContinuous_unit_isIso
    (hu : u.FullyFaithful)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso (u.sheafAdjunctionContinuous A J K).unit := sorry

/-- Sheaf pullback along a fully faithful continuous and cocontinuous functor of sites induces a
bijection on morphisms between any two sheaves. -/
@[stacks 00XU "(2)"]
theorem sheafPullback_map_bijective
    (hu : u.FullyFaithful)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (X Y : Sheaf J A) :
    Function.Bijective (fun f : X ⟶ Y => (u.sheafPullback A J K).map f) := sorry

/-- A fully faithful continuous and cocontinuous functor of sites admits a sheaf extension up to
restriction along its continuous sheaf pushforward. -/
theorem exists_sheaf_extension
    (hu : u.FullyFaithful)
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf J A) :
    ∃ F' : Sheaf K A,
      Nonempty ((u.sheafPushforwardContinuous A J K).obj F' ≅ F) := sorry

end FullyFaithful

/-- For a fully faithful continuous and cocontinuous functor of sites, every component of the unit
of the continuous sheaf adjunction is an isomorphism. -/
instance sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
    [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf J A) :
    IsIso ((u.sheafAdjunctionContinuous A J K).unit.app F) := sorry

/-- For a fully faithful continuous and cocontinuous functor of sites, every component of the
counit of the cocontinuous sheaf adjunction is an isomorphism. -/
instance sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
    [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf J A) :
    IsIso ((u.sheafAdjunctionCocontinuous A J K).counit.app F) := sorry

/-- The unit of the continuous sheaf adjunction is invertible when the site
functor is fully faithful. -/
instance sheafAdjunctionContinuous_unit_isIso_of_fullyFaithful
    [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso (u.sheafAdjunctionContinuous A J K).unit := sorry

end CategoryTheory.Functor
