/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.RingTheory.Excellent

@[expose] public section

universe u

open IsLocalRing

namespace AdicCompletion

/-- For a non-excellent regular local ring of prime characteristic with residue field finite
over its Frobenius subfield, the completion map is not formally étale. -/
theorem algebraMap_not_formallyEtale_of_not_isExcellentRing
    {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]
    [IsRegularLocalRing A] [CharP (ResidueField A) p]
    [FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
      (ResidueField A)] (h_not_excellent : ¬ IsExcellentRing.{u, u} A) :
    ¬ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
