/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Preimmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Example 26.23.10 (1): the morphism `Spec ℚ ⟶ Spec ℤ` induced by the integer
inclusion is a monomorphism. -/
@[stacks 01L9] #check
  ((IsPreimmersion.of_isLocalization (S := ℚ) (Submonoid.pos ℤ)).mono :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))

variable (S : Scheme.{u}) (s : S)

/- Example 26.23.10 (2): `Spec 𝒪_{S,s} ⟶ S` is a monomorphism. -/
@[stacks 01L9] #check (inferInstance : Mono (S.fromSpecStalk s))

end AlgebraicGeometry.Scheme
