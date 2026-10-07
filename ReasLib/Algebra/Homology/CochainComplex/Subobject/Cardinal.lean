module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.Subobject.Cardinal

@[expose] public section

/-!
# Termwise Subobject-Cardinality Bounds

The number of subobjects of each term is a property of an arbitrary homological complex. The
cochain-specific API adds stability under shifts.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u t

namespace HomologicalComplex.SubobjectCardinal

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type t} {c : ComplexShape I}

/-- A homological complex is bounded by `kappa` when every term has at most `kappa`
subobjects. Both cardinals are lifted to a common universe, so the bound itself may live in any
universe. -/
@[stacks 079K "termwise subobject cardinal"]
def BoundedBy (kappa : Cardinal.{w}) (K : HomologicalComplex C c) : Prop :=
  ∀ i,
    Cardinal.lift.{w, max u v} (Cardinal.mk (Subobject (K.X i))) ≤
      Cardinal.lift.{max u v, w} kappa

namespace BoundedBy

variable {kappa lambda : Cardinal.{w}} {K L : HomologicalComplex C c}

/-- Evaluate a termwise subobject-cardinality bound in one degree. -/
theorem degree (hK : BoundedBy kappa K) (i : I) :
    Cardinal.lift.{w, max u v} (Cardinal.mk (Subobject (K.X i))) ≤
      Cardinal.lift.{max u v, w} kappa := sorry

/-- A termwise subobject-cardinality bound remains valid after enlarging the cardinal. -/
theorem mono (hK : BoundedBy kappa K) (hkl : kappa ≤ lambda) : BoundedBy lambda K := sorry

/-- A termwise subobject-cardinality bound transports across an isomorphism of complexes. -/
theorem of_iso (hK : BoundedBy kappa K) (e : K ≅ L) : BoundedBy kappa L := sorry

/-- Isomorphic complexes satisfy the same termwise subobject-cardinality bounds. -/
theorem iso_iff (e : K ≅ L) : BoundedBy kappa K ↔ BoundedBy kappa L := sorry

/-- The ambient universe cardinal bounds the subobject lattice of every term. -/
theorem univ (K : HomologicalComplex C c) :
    BoundedBy (Cardinal.univ.{max u v, max u v + 1}) K := sorry

end BoundedBy
end General

namespace BoundedBy

section Cochain

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {kappa : Cardinal.{w}} {K : CochainComplex C ℤ}

/-- Shifting a cochain complex preserves a termwise subobject-cardinality bound. -/
theorem shift (hK : BoundedBy kappa K) (n : ℤ) :
    BoundedBy kappa ((CochainComplex.shiftFunctor C n).obj K) := sorry

end Cochain

end BoundedBy
end HomologicalComplex.SubobjectCardinal
