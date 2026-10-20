module

public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Divisibility and residue lifts over valuation rings

This leaf records the finite-divisibility and residue-linear-independence facts used in
normalization arguments over valuation rings.

@stack 09F0
-/

@[expose] public section

open IsLocalRing

universe u v

namespace ValuationRing

/-- A nonempty finite family in a valuation ring contains an element dividing every member of the
family. -/
@[stacks 09F0 "finite divisibility in a valuation ring"]
theorem exists_mem_finset_dvd_all
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {ι : Type*} (s : Finset ι) (f : ι → A) (hs : s.Nonempty) :
    ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := sorry

end ValuationRing

namespace IsExtensionOfValuationRings

/-- Residue-field linear independence of a family of lifts implies linear independence over the
base valuation ring. -/
@[stacks 09F0 "residue-independent lifts over valuation rings"]
theorem residue_linearIndependent
    {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] [ValuationRing B]
    [Algebra A B] [IsExtensionOfValuationRings A B]
    {ι : Type*} (x : ι → B)
    (hx : LinearIndependent (ResidueField A) (fun i ↦ residue B (x i))) :
    LinearIndependent A x := sorry

end IsExtensionOfValuationRings
