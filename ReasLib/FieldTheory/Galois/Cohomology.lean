/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants

@[expose] public section

universe u

open CategoryTheory.Action.ModuleCat

namespace Field

/-- Galois cohomology of a field is derived invariants for its absolute Galois group. -/
noncomputable def galoisCohomology (K : Type u) [Field K]
    (M : DiscreteModuleCat ℤ (Field.absoluteGaloisGroup K)) (n : ℕ) : ModuleCat.{u} ℤ :=
  (DiscreteModuleCat.derivedCohomologyFunctor ℤ (Field.absoluteGaloisGroup K) n).obj M

/-- Field cohomology evaluates the right derived invariants functor on the absolute Galois module. -/
theorem galoisCohomology_def (K : Type u) [Field K]
    (M : DiscreteModuleCat ℤ (Field.absoluteGaloisGroup K)) (n : ℕ) :
    galoisCohomology K M n =
      (DiscreteModuleCat.derivedCohomologyFunctor ℤ (Field.absoluteGaloisGroup K) n).obj M := sorry

end Field
