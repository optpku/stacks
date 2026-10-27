/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Monoidal
public import stacks_project.Chap96.Lemma_96_15_1_Tensor

/-! # Compatibility view of the tensor comparisons -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The étale tensor of modules with local quasi-coherence and flat base change. -/
abbrev LQCohFbc.ofModuleTensorEtale {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : LQCohFbc X) : LQCohFbc X := LQCohFbc.tensor F G

/- Remark 103.10.6: the compatibility tensor is the canonical étale tensor. -/
#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.tensor_obj :
  ∀ {X : GroupoidsOver S} [AlgebraicStack X] (F G : LQCohFbc X),
    (LQCohFbc.ofModuleTensorEtale F G).obj = moduleTensorEtale F.obj G.obj)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbc_tensorator :
  ∀ {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X),
    LQCohFbc.ofModuleTensorEtale ((QCoh.toLQCohFbc X).obj F)
      ((QCoh.toLQCohFbc X).obj G) ⟶ (QCoh.toLQCohFbc X).obj (QCoh.tensor F G))

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_μ :
  ∀ {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X),
    QCoh.tensor ((LQCohFbc.toQCoh X).obj F) ((LQCohFbc.toQCoh X).obj G) ⟶
      (LQCohFbc.toQCoh X).obj (LQCohFbc.ofModuleTensorEtale F G))

end AlgebraicGeometry.GroupoidsOver
