/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.RingTheory.Ideal.FiniteGeneration.PowerFamily

@[expose] public section

/-!
# Successive annihilator stability

The predicate in this file packages the repeated annihilator condition that
arises after quotienting by powers of the preceding entries of an ordered
finite family.
-/

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- The quotient by the `e`-th powers of the first `n` entries of an
ordered finite family. -/
@[stacks 07F8 "successive power quotient"]
abbrev PrefixPowerQuotient {r : ℕ} (π : Fin r → R) (e n : ℕ) :=
  R ⧸ Ideal.finPrefixPowerSpan π e n

/-- The class of the current entry modulo the `e`-th powers of all preceding
entries. -/
@[stacks 07F8 "successive quotient class"]
def prefixQuotientClass {r : ℕ} (π : Fin r → R) (e : ℕ) (i : Fin r) :
    PrefixPowerQuotient π e i.1 :=
  Ideal.Quotient.mk (Ideal.finPrefixPowerSpan π e i.1) (π i)

/-- The annihilator of one entry is stable after quotienting by the powered
preceding entries. -/
@[stacks 07F8 "successive annihilator stability at an index"]
def StableAnnihilator {r : ℕ} (π : Fin r → R) (e : ℕ)
    (i : Fin r) : Prop :=
  Module.IsTorsionStable
    (PrefixPowerQuotient π e i.1) (PrefixPowerQuotient π e i.1)
      (prefixQuotientClass π e i)

/-- An ordered finite family has stable annihilators with exponent `e` if,
after quotienting by the `e`-th powers of all preceding entries, the
annihilators of the current entry and its square agree. -/
@[stacks 07F8 "successive annihilator stability"]
def StableAnnihilators {r : ℕ} (π : Fin r → R) (e : ℕ) : Prop :=
  ∀ i : Fin r, StableAnnihilator π e i

/-- The empty family has stable annihilators for every exponent. -/
@[simp]
theorem stableAnnihilators_empty (e : ℕ) :
    StableAnnihilators (R := R) (fun i : Fin 0 ↦ Fin.elim0 i) e := sorry

/-- Regularity of one successive quotient class implies stability at that
index. -/
theorem stableAnnihilator_of_isSMulRegular {r : ℕ}
    (π : Fin r → R) (e : ℕ) (i : Fin r)
    (hregular :
      IsSMulRegular (PrefixPowerQuotient π e i.1) (prefixQuotientClass π e i)) :
    StableAnnihilator π e i := sorry

/-- Quotient-regularity of every successive entry implies stable
annihilators. -/
theorem StableAnnihilators.of_isSMulRegular {r : ℕ}
    (π : Fin r → R) (e : ℕ)
    (hregular : ∀ i : Fin r,
      IsSMulRegular (PrefixPowerQuotient π e i.1) (prefixQuotientClass π e i)) :
    StableAnnihilators π e := sorry

/-- Stability at one index for exponent `e * c` descends to exponent `e`
after replacing every family member by its positive `c`-th power. The
quotient transport is hidden behind the canonical prefix-power-span equality. -/
@[stacks 07FE "stable annihilator for a powered family"]
theorem StableAnnihilator.pow {r : ℕ} {π : Fin r → R} {i : Fin r}
    {e : ℕ} {c : ℕ+} (h : StableAnnihilator π (e * (c : ℕ)) i) :
    StableAnnihilator (fun j ↦ π j ^ (c : ℕ)) e i := sorry

/-- A family stable at exponent `e * c` remains stable at exponent `e`
after taking entrywise positive `c`-th powers. -/
@[stacks 07FE "stable annihilators for a powered family"]
theorem StableAnnihilators.pow {r : ℕ} {π : Fin r → R}
    {e : ℕ} {c : ℕ+} (h : StableAnnihilators π (e * (c : ℕ))) :
    StableAnnihilators (fun i ↦ π i ^ (c : ℕ)) e := sorry

/-- Stable annihilators can equivalently be stated using the canonical
`torsionBy` submodules of the successive quotient rings. -/
theorem stableAnnihilators_iff_torsionBy {r : ℕ}
    (π : Fin r → R) (e : ℕ) :
    StableAnnihilators π e ↔
      ∀ i : Fin r,
        Submodule.torsionBy (PrefixPowerQuotient π e i.1) (PrefixPowerQuotient π e i.1)
            (prefixQuotientClass π e i) =
          Submodule.torsionBy (PrefixPowerQuotient π e i.1) (PrefixPowerQuotient π e i.1)
            ((prefixQuotientClass π e i) ^ 2) := sorry

end RingTheory.Sequence
