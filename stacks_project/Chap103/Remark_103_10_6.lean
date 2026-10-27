/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Monoidal
import StacksCheckRecall

/-! # Symmetric monoidal inclusions and quasi-coherent coreflection -/

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}}

/- Remark 103.10.6: the constructed quasi-coherent coreflector is symmetric
strong monoidal, as are the inclusions of the tensor-closed module categories. -/
@[stacks 0GQM] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_braided :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.toQCoh X).Braided)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_monoidal :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.toQCoh X).Monoidal)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbc_braided :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (QCoh.toLQCohFbc X).Braided)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbc_monoidal :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (QCoh.toLQCohFbc X).Monoidal)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.inclusion_braided :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.inclusion X).Braided)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.inclusion_monoidal :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.inclusion X).Monoidal)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toFppf_braided :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.toFppf X).Braided)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toFppf_monoidal :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], (LQCohFbc.toFppf X).Monoidal)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_μ_counit_triangle :
  ∀ {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X),
    (QCoh.toLQCohFbc X).map (LQCohFbc.toQCoh_μ adj F G) ≫
      adj.counit.app (LQCohFbc.tensor F G) = LQCohFbc.toQCoh_μ_pre adj F G)
