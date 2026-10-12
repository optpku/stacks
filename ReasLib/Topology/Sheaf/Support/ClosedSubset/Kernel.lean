/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Limits
public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
public import ReasLib.Topology.Sheaf.Support
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Basic
public import ReasLib.Topology.Sheaf.Zero

/-!
# Sections with support in a closed subset: kernel model

This module defines sections vanishing on the open complement as the kernel of the canonical
restriction map. The kernel functor and its inclusion are coefficient-generic. For additive
sheaves, this kernel is the usual sheaf of sections supported on the closed subset.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe w u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{w}} {Z : Set X}
variable {C : Type u} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [IsAlgebraicStructure C (CategoryTheory.forget C)]
variable [HasColimits C] [HasZeroMorphisms C]

/-- The canonical map from a sheaf to the pushforward of its restriction to the open
complement of a closed subset. -/
abbrev restrictionToComplement
    (hZ : IsClosed Z) (F : X.Sheaf C) :
    F ⟶
      (Sheaf.pushforward C (openComplementInclusion hZ)).obj
        ((Sheaf.pullback C (openComplementInclusion hZ)).obj F) :=
  (Sheaf.pullbackPushforwardAdjunction C (openComplementInclusion hZ)).unit.app F

/-- The coefficient-generic functor of sections vanishing on the open complement of `Z`. -/
noncomputable def ambientFunctor (hZ : IsClosed Z) :
    CategoryTheory.Functor (X.Sheaf C) (X.Sheaf C) :=
  kernel (Sheaf.pullbackPushforwardAdjunction C (openComplementInclusion hZ)).unit

/-- The natural inclusion of sections vanishing on the complement into the ambient sheaf. -/
noncomputable def ambientInclusion (hZ : IsClosed Z) :
    ambientFunctor (C := C) hZ ⟶ Functor.id (X.Sheaf C) :=
  kernel.ι (Sheaf.pullbackPushforwardAdjunction C (openComplementInclusion hZ)).unit

/-- The inclusion of sections vanishing on the complement is killed by restriction to that
complement. -/
theorem ambientInclusion_condition (hZ : IsClosed Z) :
    ambientInclusion (C := C) hZ ≫
      (Sheaf.pullbackPushforwardAdjunction C (openComplementInclusion hZ)).unit = 0 := sorry

/-- The ambient sheaf of sections vanishing on the open complement. -/
abbrev object (hZ : IsClosed Z) (F : X.Sheaf C) : X.Sheaf C :=
  (ambientFunctor (C := C) hZ).obj F

/-- The canonical inclusion of sections vanishing on the complement into the ambient sheaf. -/
abbrev inclusion (hZ : IsClosed Z) (F : X.Sheaf C) : object hZ F ⟶ F :=
  (ambientInclusion (C := C) hZ).app F

/-- Every component of the ambient kernel inclusion is a monomorphism. -/
noncomputable instance inclusionMono (hZ : IsClosed Z) (F : X.Sheaf C) :
    Mono (inclusion hZ F) := sorry

/-- Remark 17.6.2 (01AY): the closed-support subobject, defined as the kernel of restriction to
the open complement. -/
@[stacks 01AY "closed-support subobject"]
noncomputable def subsheaf (hZ : IsClosed Z) (F : X.Sheaf C) : Subobject F :=
  @Subobject.mk (X.Sheaf C) _ F (object hZ F) (inclusion hZ F)
    (inclusionMono hZ F)

/-- The subobject arrow is the component of the natural ambient inclusion. -/
theorem subsheaf_arrow (hZ : IsClosed Z) (F : X.Sheaf C) :
    (@Subobject.underlyingIso (X.Sheaf C) _ (object hZ F) F (inclusion hZ F)
      (inclusionMono hZ F)).hom ≫ inclusion hZ F =
      (subsheaf hZ F).arrow := sorry

section AddCommGrp

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]

/-- Remark 17.6.2 (01AY) (1): on an open `U`, the image of the closed-support inclusion consists
exactly of the sections whose support is contained in `Z ∩ U`. -/
@[stacks 01AY "(1)"]
theorem subsheaf_app_range
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{w}) (U : Opens X) :
    Set.range ((subsheaf hZ ℱ).arrow.1.app (op U)) =
      { s | abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A local section belongs to the closed-support subsheaf exactly when its support is contained
in the closed subset. -/
theorem mem_range_inclusion_app_iff
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{w}) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    s ∈ Set.range ((subsheaf hZ ℱ).arrow.1.app (op U)) ↔
      abelianSheafSectionSupport ℱ s ⊆ { x : U | x.1 ∈ Z } := sorry

/-- The support of the closed-support subsheaf is contained in `Z`. -/
theorem support_subset
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{w}) :
    abelianSheafSupport (subsheaf hZ ℱ) ⊆ Z := sorry

/-- Any abelian subsheaf supported on `Z` is contained in the closed-support subsheaf. -/
theorem le_subsheaf_of_support_subset
    (hZ : IsClosed Z) {ℱ : X.Sheaf AddCommGrpCat.{w}} (G : Subobject ℱ)
    (hG : abelianSheafSupport G ⊆ Z) :
    G ≤ subsheaf hZ ℱ := sorry

/-- Remark 17.6.2 (01AY) (2): the closed-support subsheaf is the greatest subobject of `ℱ`
whose support is contained in `Z`. -/
@[stacks 01AY "(2)"]
theorem isGreatest_subsheaf
    (hZ : IsClosed Z) (ℱ : X.Sheaf AddCommGrpCat.{w}) :
    IsGreatest
      { G : Subobject ℱ | abelianSheafSupport G ⊆ Z }
      (subsheaf hZ ℱ) := sorry

end AddCommGrp

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
