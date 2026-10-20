/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange.Presentation

/-!
# Scalar annihilation of completed naive cotangent objects under base change

For a continuous map of Noetherian ideal pairs, a scalar annihilating the
completed naive cotangent object of a topologically finite type algebra also
annihilates the completed naive cotangent object after completed base change.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

namespace Algebra.NaiveCotangent.Adic

variable {A1 A2 B1 ι : Type u}
variable [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
variable [IsNoetherianRing A1] [IsNoetherianRing A2]
variable (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
variable (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
variable [Algebra.TopologicallyFiniteType I1 B1]
variable [Fintype ι]
variable (P : Presentation A1 B1 I1 ι)

/-- For a continuous map of Noetherian ideal pairs and a finite completed
presentation of a topologically finite type algebra, a scalar acting by zero on
the completed naive cotangent object in the derived category continues to act
by zero after canonical completed base change. -/
theorem smul_id_naiveCotangentObject_eq_zero_of_baseChange (f1 : B1)
    (hf : f1 • 𝟙 (naiveCotangentObject I1 P) = 0) :
    (includeLeftToCompletion I2 B1 f1 : completedBaseChange A1 I2 B1) •
      𝟙 (naiveCotangentObject I2 (Presentation.baseChange I1 I2 hc hI hI2 P)) = 0 := sorry

end Algebra.NaiveCotangent.Adic
