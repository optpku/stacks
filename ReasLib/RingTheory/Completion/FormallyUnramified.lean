module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import ReasLib.FieldTheory.Frobenius.Subfield

@[expose] public section

universe u

open IsLocalRing

namespace AdicCompletion

/-- The completion of a Noetherian local ring of prime characteristic with residue field finite
over its Frobenius subfield is formally unramified over the original ring. -/
instance instFormallyUnramified {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
    [CharP A p] [IsNoetherianRing A] [IsLocalRing A] [CharP (ResidueField A) p]
    [FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
      (ResidueField A)] :
    Algebra.FormallyUnramified A (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
