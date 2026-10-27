/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
import StacksCheckRecall

/-! # The quasi-coherent coreflector on an algebraic stack -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}}

/- Lemma 103.10.1 (1): The inclusion of quasi-coherent modules into locally
quasi-coherent étale modules with flat base change has a right adjoint. -/
@[stacks 0778] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbc_isLeftAdjoint :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X], (QCoh.toLQCohFbc X).IsLeftAdjoint)

/- Lemma 103.10.1 (2): Inclusion followed by the constructed right adjoint
is naturally isomorphic to the identity on quasi-coherent modules. -/
@[stacks 0778] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbc_comp_toQCoh :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X],
      QCoh.toLQCohFbc X ⋙ LQCohFbc.toQCoh X ≅ 𝟭 (QCoh X))
