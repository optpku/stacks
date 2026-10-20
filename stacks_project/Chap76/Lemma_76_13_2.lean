/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry

universe u v

/- Lemma 76.13.2: Let `S` be a scheme. Let `a : F ⟶ G` be a transformation of
functors `F, G : (Over S)ᵒᵖ ⥤ Type`. Then `a` is formally étale if and only if
`a` is both formally smooth and formally unramified. -/
@[stacks 04G4]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.iff_formallySmooth_and_formallyUnramified :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G),
      AlgebraicGeometry.Scheme.Over.FormallyEtale a ↔
        AlgebraicGeometry.Scheme.Over.FormallySmooth a ∧
          AlgebraicGeometry.Scheme.Over.FormallyUnramified a)
