/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing.Adjunction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.10.7. In Situation 81.10.6, the reverse kernel functor is right
adjoint to the canonical glueing functor. -/
@[stacks 0AEY] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functorReverseAdjunction :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
      [QuasiCompact f] → [QuasiSeparated f] → [IsClosedImmersion i] →
      [FinitePresentation i] → [IsFormalGlueing f i] →
      AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor f i ⊣
        AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.reverse f i)
