/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType

namespace NumericalType

/-- The componentwise preservation conditions for a relabeling of numerical types. -/
public structure IsRelabeling (T T' : NumericalType) (e : Fin T.n ≃ Fin T'.n) : Prop where
  /-- Relabeling preserves multiplicities. -/
  multiplicity_eq : ∀ i, T.multiplicity i = T'.multiplicity (e i)
  /-- Relabeling preserves intersection-matrix entries. -/
  intersection_eq : ∀ i j, T.intersection i j = T'.intersection (e i) (e j)
  /-- Relabeling preserves weights. -/
  weight_eq : ∀ i, T.weight i = T'.weight (e i)
  /-- Relabeling preserves component genera. -/
  componentGenus_eq : ∀ i, T.componentGenus i = T'.componentGenus (e i)

/-- Construct a data-preserving relabeling from its four componentwise equalities. -/
public def IsRelabeling.of {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n}
    (multiplicity_eq : ∀ i, T.multiplicity i = T'.multiplicity (e i))
    (intersection_eq : ∀ i j,
      T.intersection i j = T'.intersection (e i) (e j))
    (weight_eq : ∀ i, T.weight i = T'.weight (e i))
    (componentGenus_eq : ∀ i,
      T.componentGenus i = T'.componentGenus (e i)) :
    IsRelabeling T T' e :=
  { multiplicity_eq, intersection_eq, weight_eq, componentGenus_eq }

namespace IsRelabeling

/-- The identity equivalence relabels a numerical type to itself. -/
public theorem refl (T : NumericalType) : IsRelabeling T T (Equiv.refl (Fin T.n)) := sorry

end IsRelabeling

/-- Two numerical types are equivalent when some relabeling preserves all their data. -/
public def Equivalent (T T' : NumericalType) : Prop :=
  ∃ e : Fin T.n ≃ Fin T'.n, IsRelabeling T T' e

/-- Equivalence is characterized by the existence of a data-preserving relabeling. -/
public theorem equivalent_iff_exists_relabeling (T T' : NumericalType) :
    Equivalent T T' ↔ ∃ e : Fin T.n ≃ Fin T'.n, IsRelabeling T T' e := sorry

/-- Every numerical type is equivalent to itself. -/
public theorem equivalent_refl (T : NumericalType) : Equivalent T T := sorry

/-- Equivalence of numerical types is symmetric. -/
public theorem equivalent_symm {T T' : NumericalType} : Equivalent T T' → Equivalent T' T := sorry

/-- Equivalence of numerical types is transitive. -/
public theorem equivalent_trans {T T' T'' : NumericalType} :
    Equivalent T T' → Equivalent T' T'' → Equivalent T T'' := sorry

/-- The explicit setoid of numerical types modulo data-preserving relabeling. -/
public def setoid : Setoid NumericalType where
  r := Equivalent
  iseqv := sorry

/-- The relation of `NumericalType.setoid` is equivalence under relabeling. -/
public theorem setoid_rel (T T' : NumericalType) : setoid.r T T' ↔ Equivalent T T' := sorry

end NumericalType
