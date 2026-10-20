/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-! # Trivial Brauer Group over Algebraically Closed Fields

Over an algebraically closed field, the Brauer group is trivial: every
finite-dimensional central simple algebra is Brauer equivalent to the base field.

## Main declarations

- `CSA.brauerEquivalent_one` — every CSA over an algebraically closed field is
  Brauer equivalent to the unit class
- `BrauerGroup.eq_one_of_isAlgClosed` — quotient-level triviality
- `BrauerGroup.subsingleton` — `Br(k)` is subsingleton when `k` is algebraically closed

## References

- [Stacks Project, Tag 074M](https://stacks.math.columbia.edu/tag/074M)

@stack 074M
-/

@[expose] public section

noncomputable section

universe u v

open Matrix

namespace CSA

section

variable (k : Type u) [Field k] [IsAlgClosed k]

private theorem brauerEquivalent_baseField_small (A : CSA.{u, u} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k A
  refine ⟨1, n, one_ne_zero, hn.ne, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans e⟩

omit [IsAlgClosed k] in
private theorem smallCarrierOfCSA (A : CSA.{u, v} k) : Small.{u} (↑A.toAlgCat) :=
  Small.mk' (Module.finBasis k A).equivFun.toEquiv

omit [IsAlgClosed k] in
private def shrinkCSA (A : CSA.{u, v} k) : CSA.{u, u} k :=
  letI := smallCarrierOfCSA k A
  { toAlgCat := AlgCat.of k (Shrink.{u} (↑A.toAlgCat))
    isCentral := by
      let e : Shrink.{u} (↑A.toAlgCat) ≃ₐ[k] ↑A.toAlgCat := Shrink.algEquiv k (↑A.toAlgCat)
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : e x ∈ Subalgebra.center k (↑A.toAlgCat) := by
        rw [Subalgebra.mem_center_iff] at hx ⊢
        intro b
        have hcomm : e.symm b * x = x * e.symm b := hx (e.symm b)
        exact by simpa using congrArg e hcomm
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hx'
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      have hxe : e x = e (algebraMap k (Shrink.{u} (↑A.toAlgCat)) a) := by
        simpa using ha
      exact e.injective hxe.symm
    isSimple := IsSimpleRing.of_ringEquiv (Shrink.ringEquiv (↑A.toAlgCat)).symm inferInstance
    fin_dim := (Shrink.algEquiv k (↑A.toAlgCat)).symm.toLinearEquiv.finiteDimensional }

omit [IsAlgClosed k] in
private def shrinkAlgEquiv (A : CSA.{u, v} k) : shrinkCSA k A ≃ₐ[k] A :=
  letI := smallCarrierOfCSA k A
  Shrink.algEquiv k (↑A.toAlgCat)

omit [IsAlgClosed k] in
private theorem brauerEquivalent_shrink (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (shrinkCSA k A) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans <|
    (shrinkAlgEquiv k A).symm.trans <|
      ((reindexAlgEquiv k (shrinkCSA k A) finOneEquiv).trans uniqueAlgEquiv).symm⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3, representative-level bridge: over an algebraically closed field, every
finite-dimensional central simple `k`-algebra is Brauer equivalent to the base field. -/
@[stacks 074M]
theorem brauerEquivalent_one (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  exact IsBrauerEquivalent.trans (brauerEquivalent_shrink k A)
    (brauerEquivalent_baseField_small k (shrinkCSA k A))

private theorem brauerEquivalent_baseField_unit (k : Type u) [Field k] :
    IsBrauerEquivalent (CSA.mk (AlgCat.of k k)) (CSA.unit k) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k (CSA.mk (AlgCat.of k k)) finOneEquiv).trans uniqueAlgEquiv).trans <|
    (ULift.algEquiv : ↑(CSA.unit k).toAlgCat ≃ₐ[k] k).symm.trans <|
      ((reindexAlgEquiv k (CSA.unit k) finOneEquiv).trans uniqueAlgEquiv).symm⟩

/-- Companion bridge: over an algebraically closed field, every finite-dimensional central simple
`k`-algebra is Brauer equivalent to the canonical neutral representative `CSA.unit k`. -/
theorem brauerEquivalent_unit (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent A (CSA.unit k) := by
  exact IsBrauerEquivalent.trans A.brauerEquivalent_one (brauerEquivalent_baseField_unit k)

end

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3: if `k` is algebraically closed, then every Brauer class over `k` is the unit
class. -/
@[stacks 074M]
theorem eq_one_of_isAlgClosed (A : Br(k)) : A = 1 := by
  refine Quotient.inductionOn A fun A ↦ ?_
  rw [one_def]
  exact Quotient.sound A.brauerEquivalent_unit

instance subsingleton [IsAlgClosed k] : Subsingleton (Br(k)) := by
  refine ⟨fun A B ↦ ?_⟩
  rw [A.eq_one_of_isAlgClosed, B.eq_one_of_isAlgClosed]

end BrauerGroup

end
