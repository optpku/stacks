/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]

/- Lemma 29.36.12

An étale morphism is flat.
-/
@[stacks 02GS] #check
  (AlgebraicGeometry.instFlatOfSmooth (f := f) : AlgebraicGeometry.Flat f)

end AlgebraicGeometry
