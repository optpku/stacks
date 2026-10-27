/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Exactness
import StacksCheckRecall

/-!
# Kernel of the right adjoint to quasi-coherent inclusion

The quasi-coherent coreflector has parasitic kernel and parasitic counit
kernel and cokernel, is exact, and preserves limits and universe-compatible colimits.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver

universe u v w

variable {S : Scheme.{u}}

/- Lemma 103.10.2 (1): The kernel of the quasi-coherent coreflector is exactly
the collection of parasitic objects. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_kernel :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X],
      Functor.kernel (LQCohFbc.toQCoh X) = LQCohFbc.parasitic X)

/- Lemma 103.10.2 (2): The kernel of the canonical adjunction map is parasitic. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_counit_kernel_isParasitic :
    ∀ {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X),
      LQCohFbc.parasitic X (kernel ((QCoh.toLQCohFbcAdjunction X).counit.app F)))

/- Lemma 103.10.2 (3): The cokernel of the canonical adjunction map is parasitic. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_counit_cokernel_isParasitic :
    ∀ {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X),
      LQCohFbc.parasitic X (cokernel ((QCoh.toLQCohFbcAdjunction X).counit.app F)))

/- Lemma 103.10.2 (4): The quasi-coherent coreflector is exact. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_exact :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X],
      exactFunctor (LQCohFbc X) (QCoh X) (LQCohFbc.toQCoh X))

/- Lemma 103.10.2 (5): The quasi-coherent coreflector preserves all limits. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_preservesLimits :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X],
      PreservesLimitsOfSize.{v, w} (LQCohFbc.toQCoh X))

/- Lemma 103.10.2 (6): The quasi-coherent coreflector preserves colimits of
every size supported by the ambient category of abelian groups. -/
@[stacks 0779] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_preservesColimits :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X]
      [HasColimitsOfSize.{v, w} AddCommGrpCat.{u}],
      PreservesColimitsOfSize.{v, w} (LQCohFbc.toQCoh X))
