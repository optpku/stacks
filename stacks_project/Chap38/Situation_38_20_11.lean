/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}}
variable (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable (T : Over S)

/- Situation 38.20.11: base change defines a subterminal contravariant functor on schemes
over `S`, recording where `ℱ` is flat over the new base in dimensions at least `n`. -/
@[stacks 05MT] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor f ℱ n :
    (Over S)ᵒᵖ ⥤ Type u)

#check AlgebraicGeometry.Scheme.Modules.baseChangeModule f T.hom ℱ

#check AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor_nonempty_iff f ℱ n T

#check AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor_isEmpty_iff f ℱ n T

#check AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor_obj_subsingleton f ℱ n T
