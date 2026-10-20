/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsAffine X] [IsAffine S]

/- Lemma 37.11.6: For a morphism of affine schemes, formal smoothness is equivalent
to formal smoothness of the induced map on global sections. -/
@[stacks 02H4] #check (AlgebraicGeometry.FormallySmooth.iff_of_isAffine (f := f) :
  FormallySmooth f ↔ f.appTop.hom.FormallySmooth)
