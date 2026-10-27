/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector

/-! # Exactness and parasitic kernel of the quasi-coherent coreflector -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Parasitic objects of `LQCohFbc X` are those whose underlying étale modules
are parasitic. -/
abbrev LQCohFbc.parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (LQCohFbc X) :=
  (EtaleModules.parasitic X).inverseImage (LQCohFbc.inclusion X)

/-- An object of `LQCohFbc X` is parasitic if and only if its underlying étale
module is parasitic. -/
theorem LQCohFbc.mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : LQCohFbc X) :
    LQCohFbc.parasitic X F ↔
      EtaleModules.IsParasitic ((LQCohFbc.inclusion X).obj F) := sorry

/-- The kernel of the quasi-coherent coreflector consists exactly of the
parasitic objects. -/
theorem LQCohFbc.toQCoh_kernel (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.kernel (LQCohFbc.toQCoh X) = LQCohFbc.parasitic X := sorry

/-- An object becomes zero under the quasi-coherent coreflector if and only
if it is parasitic. -/
theorem LQCohFbc.toQCoh_isZero_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : LQCohFbc X) :
    IsZero ((LQCohFbc.toQCoh X).obj F) ↔ LQCohFbc.parasitic X F := sorry

/-- The kernel of the canonical quasi-coherent coreflection counit is
parasitic. -/
theorem LQCohFbc.toQCoh_counit_kernel_isParasitic
    {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X) :
    LQCohFbc.parasitic X
      (kernel ((QCoh.toLQCohFbcAdjunction X).counit.app F)) := sorry

/-- The cokernel of the canonical quasi-coherent coreflection counit is
parasitic. -/
theorem LQCohFbc.toQCoh_counit_cokernel_isParasitic
    {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X) :
    LQCohFbc.parasitic X
      (cokernel ((QCoh.toLQCohFbcAdjunction X).counit.app F)) := sorry

/-- The quasi-coherent coreflector preserves finite limits and finite colimits. -/
theorem LQCohFbc.toQCoh_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (LQCohFbc X) (QCoh X) (LQCohFbc.toQCoh X) := sorry

/-- The quasi-coherent coreflector preserves limits of every diagram size. -/
instance LQCohFbc.toQCoh_preservesLimits (X : GroupoidsOver S)
    [AlgebraicStack X] :
    PreservesLimitsOfSize.{v, w} (LQCohFbc.toQCoh X) := sorry

/-- The quasi-coherent coreflector preserves colimits of every size for which
the ambient category of abelian groups has colimits. -/
instance LQCohFbc.toQCoh_preservesColimits (X : GroupoidsOver S)
    [AlgebraicStack X] [HasColimitsOfSize.{v, w} AddCommGrpCat.{u}] :
    PreservesColimitsOfSize.{v, w} (LQCohFbc.toQCoh X) := sorry

end AlgebraicGeometry.GroupoidsOver
