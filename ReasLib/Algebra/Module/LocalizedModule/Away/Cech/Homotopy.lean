module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
public import ReasLib.Algebra.Homology.Homotopy.Contractible
public import ReasLib.AlgebraicTopology.Cech.Conerve.SplitMono.Homotopy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.AlternatingCoface
import Mathlib.Tactic.CrossRefAttribute

/-!
# Contractibility of an extended alternating Cech complex

The split-monomorphism and homotopy-equivalence consequences of a unit entry in a principal-open
family are owned here.  The construction of the family map and of the extended complex remains in
`LocalizedModule.Away.Cech` and `LocalizedModule.Away.Cech.Alternating`; chapter files only provide
source-facing aliases.

@stack 0G6J
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace LocalizedModule.Away.Cech.Alternating

variable {R : Type u} [CommRing R]
variable {r : ℕ}

namespace familyMap

variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-! The unit-entry criterion is stated for the canonical family map itself, rather than for a
chapter-local spelling of that map. -/

/-- Lemma 15.29.4 (Stacks `0G6J`): a unit entry makes the canonical principal-open family map a
split monomorphism. -/
@[stacks 0G6J "unit entry gives a split-mono Cech family map"]
theorem isSplitMono_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    IsSplitMono (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap M f)) := sorry

end familyMap

namespace extended

variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-- Lemma 15.29.4 (Stacks `0G6J`): a unit entry makes the extended alternating Cech complex
contractible in the canonical homological-complex sense. -/
@[stacks 0G6J "unit entry gives a contractible extended alternating Cech complex"]
theorem isContractible_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    (extended f M).Contractible := sorry

/-- Lemma 15.29.4 (Stacks `0G6J`): a unit entry makes the extended alternating Cech complex
homotopy equivalent to the zero cochain complex. -/
@[stacks 0G6J "unit entry gives a homotopy equivalence to zero"]
theorem homotopyEquivalent_zero_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extended f M)
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} R) ℕ)) := sorry

/-- Lemma 15.29.4 (Stacks `0G6J`): it suffices that one member of the finite family is a unit. -/
@[stacks 0G6J "some unit entry gives a homotopy equivalence to zero"]
theorem homotopyEquivalent_zero_of_exists_isUnit
    (f : Fin r → R) (hunit : ∃ i : Fin r, IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extended f M)
        (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} R) ℕ)) := sorry

end extended

end LocalizedModule.Away.Cech.Alternating

end
