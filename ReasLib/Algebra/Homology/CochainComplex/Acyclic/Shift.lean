module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

@[expose] public section

/-!
# Acyclic Complexes and Shifts

This module exposes the isomorphism and shift stability of acyclicity independently of any
smallness or boundedness condition.
-/

open CategoryTheory

universe v u t

namespace HomologicalComplex.Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type t} {c : ComplexShape I} {K L : HomologicalComplex C c}

/-- Acyclicity is invariant under isomorphism of homological complexes. -/
theorem of_iso (hK : K.Acyclic) (e : K ≅ L) : L.Acyclic := sorry

end HomologicalComplex.Acyclic

namespace CochainComplex.Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A shift of an acyclic cochain complex is acyclic. -/
@[stacks 079K "acyclic shifts"]
theorem shift {K : CochainComplex C ℤ} (hK : K.Acyclic) (n : ℤ) :
    (K⟦n⟧).Acyclic := sorry

end CochainComplex.Acyclic
