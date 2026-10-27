/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import ReasLib.Algebra.Homology.CochainComplex.Acyclic.Shift
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.Subobject.Cardinal

@[expose] public section

/-!
# Cardinal Bounds for Small Acyclic Cochain Complexes

This module separates the property of one bounded-above acyclic complex from the two uniform
cardinal bounds used to find subcomplexes and coproduct presentations, and names the condition
that one cardinal satisfies both bounds.
-/

open CategoryTheory CategoryTheory.Limits

universe w z v u

namespace CochainComplex.SmallAcyclic

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A bounded-above acyclic cochain complex whose termwise subobject cardinals are bounded by
`kappa`. -/
@[stacks 079K "small acyclic complex"]
def BoundedBy (kappa : Cardinal.{z}) (K : CochainComplex C ℤ) : Prop :=
  CochainComplex.minus C K ∧
    K.Acyclic ∧ HomologicalComplex.SubobjectCardinal.BoundedBy kappa K

namespace BoundedBy

variable {kappa lambda : Cardinal.{z}} {K L : CochainComplex C ℤ}

/-- A small acyclic complex is bounded above. -/
theorem minus (hK : BoundedBy kappa K) : CochainComplex.minus C K := hK.1

/-- A small acyclic complex is acyclic. -/
theorem acyclic (hK : BoundedBy kappa K) : K.Acyclic := hK.2.1

/-- A small acyclic complex satisfies its termwise subobject-cardinality bound. -/
theorem cardinal (hK : BoundedBy kappa K) :
    HomologicalComplex.SubobjectCardinal.BoundedBy kappa K := hK.2.2

/-- Evaluate the subobject-cardinality bound of a small acyclic complex in one degree. -/
theorem cardinal_at (hK : BoundedBy kappa K) (i : ℤ) :
    Cardinal.lift.{z, max u v} (Cardinal.mk (Subobject (K.X i))) ≤
      Cardinal.lift.{max u v, z} kappa := hK.2.2 i

/-- A small acyclic complex remains small after enlarging the cardinal bound. -/
theorem mono (hK : BoundedBy kappa K) (hkl : kappa ≤ lambda) : BoundedBy lambda K :=
  ⟨hK.1, hK.2.1, hK.2.2.mono hkl⟩

/-- Small acyclicity transports across an isomorphism of cochain complexes. -/
theorem of_iso (hK : BoundedBy kappa K) (e : K ≅ L) : BoundedBy kappa L := by
  obtain ⟨n, hn⟩ := hK.1
  -- Local instance justification (proof-local temporary data): The support bound extracted from the existential is consumed by the native isStrictlyLE_of_iso theorem.
  haveI := hn
  exact ⟨⟨n, CochainComplex.isStrictlyLE_of_iso e n⟩,
    fun i ↦ (hK.2.1 i).of_iso e, hK.2.2.of_iso e⟩

/-- Shifting preserves bounded-above acyclic complexes with a fixed termwise cardinal bound. -/
theorem shift (hK : BoundedBy kappa K) (n : ℤ) : BoundedBy kappa (K⟦n⟧) := by
  refine ⟨(CochainComplex.minus C).le_shift n K hK.1, ?_, hK.2.2.shift n⟩
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
  exact (HomotopyCategory.subcategoryAcyclic C).prop_of_iso
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).le_shift n _
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).mpr hK.2.1))

end BoundedBy

/-- A uniform bound for finding nonzero small acyclic subcomplexes inside nonzero acyclic
complexes. -/
@[stacks 079K "small acyclic subcomplex bound"]
def HasSubcomplexes (C : Type u) [Category.{v} C] [Abelian C]
    (kappa : Cardinal.{z}) : Prop :=
  ∀ (M : CochainComplex C ℤ) (_ : M.Acyclic) (_ : ¬ IsZero M),
    ∃ N : Subobject M,
      ¬ IsZero (N : CochainComplex C ℤ) ∧ BoundedBy kappa (N : CochainComplex C ℤ)

/-- A uniform bound for presenting acyclic complexes as quotients of coproducts of small
acyclic complexes. -/
@[stacks 079K "acyclic coproduct presentation bound"]
def HasCoproductPresentations (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C]
    (kappa : Cardinal.{z}) : Prop :=
  ∀ (M : CochainComplex C ℤ) (_ : M.Acyclic),
    ∃ (I : Type w) (K : I → CochainComplex C ℤ) (f : (∐ fun i ↦ K i) ⟶ M),
      Epi f ∧ ∀ i, BoundedBy kappa (K i)

/-- A cardinal is a uniform small-acyclic bound when it simultaneously controls nonzero acyclic
subcomplexes and coproduct presentations of arbitrary acyclic complexes. -/
@[stacks 079K "uniform small acyclic bound"]
def IsUniformBound (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (kappa : Cardinal.{z}) : Prop :=
  HasSubcomplexes C kappa ∧ HasCoproductPresentations C kappa

/-- A cardinal is a uniform small-acyclic bound exactly when it has the subcomplex and
coproduct-presentation properties. -/
theorem isUniformBound_iff (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (kappa : Cardinal.{z}) :
    IsUniformBound C kappa ↔
      HasSubcomplexes C kappa ∧ HasCoproductPresentations C kappa := Iff.rfl

namespace HasSubcomplexes

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A uniform subcomplex bound remains valid after enlarging its cardinal. -/
theorem mono {kappa lambda : Cardinal.{z}} (h : HasSubcomplexes C kappa)
    (hkl : kappa ≤ lambda) : HasSubcomplexes C lambda := by
  intro M hM hne
  obtain ⟨N, hN, hb⟩ := h M hM hne
  exact ⟨N, hN, hb.mono hkl⟩

end HasSubcomplexes

namespace HasCoproductPresentations

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasCoproducts.{w} C]

/-- A uniform coproduct-presentation bound remains valid after enlarging its cardinal. -/
theorem mono {kappa lambda : Cardinal.{z}}
    (h : HasCoproductPresentations C kappa) (hkl : kappa ≤ lambda) :
    HasCoproductPresentations C lambda := by
  intro M hM
  obtain ⟨I, K, f, hf, hK⟩ := h M hM
  exact ⟨I, K, f, hf, fun i ↦ (hK i).mono hkl⟩

end HasCoproductPresentations

namespace IsUniformBound

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {kappa lambda : Cardinal.{z}}

/-- A uniform small-acyclic bound supplies bounded nonzero acyclic subcomplexes. -/
theorem hasSubcomplexes (h : IsUniformBound C kappa) : HasSubcomplexes C kappa := h.1

/-- A uniform small-acyclic bound supplies coproduct presentations by bounded acyclic
complexes. -/
theorem hasCoproductPresentations (h : IsUniformBound C kappa) :
    HasCoproductPresentations C kappa := h.2

/-- A uniform small-acyclic bound remains valid after enlarging the cardinal. -/
theorem mono (h : IsUniformBound C kappa) (hkl : kappa ≤ lambda) :
    IsUniformBound C lambda := ⟨h.1.mono hkl, h.2.mono hkl⟩

end IsUniformBound

end CochainComplex.SmallAcyclic
