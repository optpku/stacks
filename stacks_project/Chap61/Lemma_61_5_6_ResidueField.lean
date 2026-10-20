module

public import ReasLib.RingTheory.Algebraic.ResidueField

/-! This source-facing module preserves the established residue-field API. -/

@[expose] public section

universe u v

/- Lemma 61.5.6 residue-field predicate bridge. -/
#check (Algebra.IsAlgebraicOnResidueFields :
  (R : Type u) → (S : Type v) → [CommRing R] → [CommRing S] → [Algebra R S] → Prop)
