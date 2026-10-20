/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

universe u

namespace IsJacobsonRing

/-- There exists a Jacobson, universally catenary domain with maximal ideals whose
localizations have Krull dimensions one and two, respectively. -/
theorem exists_universallyCatenaryDomain_maximals_ringKrullDim_one_two :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsJacobsonRing B)
      (_ : UniversallyCatenaryRing.{u, u} B) (m1 m2 : Ideal B)
      (_ : m1.IsMaximal) (_ : m2.IsMaximal),
      ringKrullDim (Localization.AtPrime m1) = 1 ∧
        ringKrullDim (Localization.AtPrime m2) = 2 := sorry

end IsJacobsonRing
