/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.SerreQuotient
import StacksCheckRecall

/-!
# Remark 103.10.7

On an algebraic stack, `QCoh` is the Serre quotient of `LQCoh^{fbc}` by parasitic
objects, and the inclusion `QCoh.toLQCohFbc` is left adjoint to that quotient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.parasitic_isSerreClass :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], IsSerreClass (LQCohFbc.parasitic X))

/- Remark 103.10.7 (1): The quasi-coherent coreflector identifies `QCoh X`
with the Serre quotient of `LQCohFbc X` by parasitic objects. -/
@[stacks 07B2] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_isLocalization :
    ∀ (X : GroupoidsOver S) [AlgebraicStack X],
      (LQCohFbc.toQCoh X).IsLocalization (LQCohFbc.parasitic X).isoModSerre)

/- Remark 103.10.7 (2): The inclusion of quasi-coherent modules is left
adjoint to the quotient coreflector. The derived-category analogue is the
forward reference to Lemma 104.5.4. -/
@[stacks 07B2] #check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbcAdjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
