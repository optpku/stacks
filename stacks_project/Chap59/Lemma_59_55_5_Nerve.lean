/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.CechDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.55.5: the iterated fibre products form the canonical scheme-valued Čech nerve. -/
@[stacks 09Z2] #check (AlgebraicGeometry.Scheme.Etale.finiteCechNerve :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [(Arrow.mk f).HasCechNerve],
    SimplicialObject Scheme.{u})

end AlgebraicGeometry.Scheme.Etale
