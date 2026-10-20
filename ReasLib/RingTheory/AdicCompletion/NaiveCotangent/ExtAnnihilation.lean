/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange.Presentation

/-!
# Ext¹ annihilation of completed naive cotangent objects after base change

Continuous maps of Noetherian adic pairs preserve universal Ext¹ annihilation
of completed naive cotangent objects under completed base change.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

namespace Algebra.NaiveCotangent.Adic

variable {A1 A2 B1 ι : Type u}
variable [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
variable [IsNoetherianRing A1] [IsNoetherianRing A2]
variable (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
variable (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2)
variable [Algebra.TopologicallyFiniteType I1 B1]
variable [Fintype ι]
variable (P : Presentation A1 B1 I1 ι)

/-- For a continuous map of Noetherian adic pairs and a finite completed
presentation of an adically complete algebra with finite-type special fiber,
if `f1` annihilates Ext¹ from its completed naive cotangent object against every
module, then the image of `f1` annihilates Ext¹ from the completed naive
cotangent object of the canonical completed base change against every module. -/
theorem twoTermExtOneAnnihilatedByIdeal_of_baseChange (f1 : B1)
    (hf : twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject I1 P) (Ideal.span {f1})) :
    twoTermExtOneAnnihilatedByIdeal
      (naiveCotangentObject I2
        (Presentation.baseChange I1 I2 hc hI I2.fg_of_isNoetherianRing P))
      (Ideal.span {includeLeftToCompletion I2 B1 f1}) := sorry

end Algebra.NaiveCotangent.Adic
