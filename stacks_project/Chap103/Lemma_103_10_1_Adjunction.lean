/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector

/-! # Presentation reconstruction and the quasi-coherent adjunction -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.AlgebraicStack

universe u

variable {S : Scheme.{u}}

/- Presentation pullback has the concrete compatible-section extension as inverse. -/
#check (AlgebraicGeometry.AlgebraicStack.Presentation.qcohEquivalence :
  ∀ {X : GroupoidsOver S} [AlgebraicStack X] (P : Presentation X),
    QCoh X ≌ QCoh (SmallQuotient.quotientStack P.groupoid))

/- The quasi-coherent functor is descent followed by explicit reconstruction. -/
#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_eq :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    LQCohFbc.toQCoh X = LQCohFbc.toGroupoidModules X ⋙
      QuotientQCoh.fromGroupoidStack (algebraicStackPresentation X).groupoid ⋙
        (Presentation.qcohEquivalence (algebraicStackPresentation X)).inverse)

/- The actual inclusion is adjoint to the specified reconstruction functor. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCohFbcAdjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X], QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
