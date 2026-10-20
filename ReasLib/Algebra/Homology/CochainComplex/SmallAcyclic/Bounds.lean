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
theorem minus (hK : BoundedBy kappa K) : CochainComplex.minus C K := sorry

/-- A small acyclic complex is acyclic. -/
theorem acyclic (hK : BoundedBy kappa K) : K.Acyclic := sorry

/-- A small acyclic complex satisfies its termwise subobject-cardinality bound. -/
theorem cardinal (hK : BoundedBy kappa K) :
    HomologicalComplex.SubobjectCardinal.BoundedBy kappa K := sorry

/-- Evaluate the subobject-cardinality bound of a small acyclic complex in one degree. -/
theorem cardinal_at (hK : BoundedBy kappa K) (i : ℤ) :
    Cardinal.lift.{z, max u v} (Cardinal.mk (Subobject (K.X i))) ≤
      Cardinal.lift.{max u v, z} kappa := sorry

/-- A small acyclic complex remains small after enlarging the cardinal bound. -/
theorem mono (hK : BoundedBy kappa K) (hkl : kappa ≤ lambda) : BoundedBy lambda K := sorry

/-- Small acyclicity transports across an isomorphism of cochain complexes. -/
theorem of_iso (hK : BoundedBy kappa K) (e : K ≅ L) : BoundedBy kappa L := sorry

/-- Shifting preserves bounded-above acyclic complexes with a fixed termwise cardinal bound. -/
theorem shift (hK : BoundedBy kappa K) (n : ℤ) : BoundedBy kappa (K⟦n⟧) := sorry

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
      HasSubcomplexes C kappa ∧ HasCoproductPresentations C kappa := sorry

namespace HasSubcomplexes

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A uniform subcomplex bound remains valid after enlarging its cardinal. -/
theorem mono {kappa lambda : Cardinal.{z}} (h : HasSubcomplexes C kappa)
    (hkl : kappa ≤ lambda) : HasSubcomplexes C lambda := sorry

end HasSubcomplexes

namespace HasCoproductPresentations

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasCoproducts.{w} C]

/-- A uniform coproduct-presentation bound remains valid after enlarging its cardinal. -/
theorem mono {kappa lambda : Cardinal.{z}}
    (h : HasCoproductPresentations C kappa) (hkl : kappa ≤ lambda) :
    HasCoproductPresentations C lambda := sorry

end HasCoproductPresentations

namespace IsUniformBound

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {kappa lambda : Cardinal.{z}}

/-- A uniform small-acyclic bound supplies bounded nonzero acyclic subcomplexes. -/
theorem hasSubcomplexes (h : IsUniformBound C kappa) : HasSubcomplexes C kappa := sorry

/-- A uniform small-acyclic bound supplies coproduct presentations by bounded acyclic
complexes. -/
theorem hasCoproductPresentations (h : IsUniformBound C kappa) :
    HasCoproductPresentations C kappa := sorry

/-- A uniform small-acyclic bound remains valid after enlarging the cardinal. -/
theorem mono (h : IsUniformBound C kappa) (hkl : kappa ≤ lambda) :
    IsUniformBound C lambda := sorry

end IsUniformBound

end CochainComplex.SmallAcyclic
