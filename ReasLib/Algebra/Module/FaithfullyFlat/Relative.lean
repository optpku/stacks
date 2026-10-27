/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Faithful flatness along a ring homomorphism

Faithful flatness along an explicit ring homomorphism uses the scalar action obtained by
restriction of scalars.
-/

@[expose] public section

universe u v w

namespace Module

/-- Faithful flatness of an `A`-module after restricting scalars along `f : R →+* A`. -/
def FaithfullyFlatAlong {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  @Module.FaithfullyFlat R M _ _ (Module.compHom M f)

/-- Faithful flatness along a ring homomorphism is faithful flatness for the restricted
scalar action. -/
theorem faithfullyFlatAlong_iff {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) (M : Type w) [AddCommGroup M] [Module A M] :
    FaithfullyFlatAlong f M ↔ @Module.FaithfullyFlat R M _ _ (Module.compHom M f) := sorry

end Module
