module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.RingTheory.Excellent

@[expose] public section

universe u

open IsLocalRing
open FieldExtension.Frobenius

namespace IsRegularLocalRing

/-- A regular local ring of prime characteristic whose residue field is finite over its
Frobenius subfield is excellent if and only if its canonical maximal-ideal completion map
is formally étale. -/
@[stacks 0G68]
theorem isExcellentRing_iff_algebraMap_formallyEtale
    {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]
    [IsRegularLocalRing A] [CharP (ResidueField A) p]
    [FiniteDimensional (subfield p (ResidueField A)) (ResidueField A)] :
    IsExcellentRing.{u, u} A ↔
      Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := sorry

end IsRegularLocalRing
