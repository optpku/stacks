/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.CycleGroup
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (f : X ⟶ Y) [IsProper f.left] (k : ℤ)

/- Definition 42.12.1: Proper pushforward sends a degree-`k` cycle on `X` to the
degree-`k` cycle on `Y` obtained by sending an integral generator to zero when its image
drops dimension, and otherwise weighting the image by the corresponding residue-field degree. -/
@[stacks 02R4] #check
  (AlgebraicGeometry.CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
    (Y.hom.relativeDimensionFunction δ) k :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) k →+
      CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)

end
