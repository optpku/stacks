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
public theorem refl (T : NumericalType) : IsRelabeling T T (Equiv.refl (Fin T.n)) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

end IsRelabeling

/-- Two numerical types are equivalent when some relabeling preserves all their data. -/
public def Equivalent (T T' : NumericalType) : Prop :=
  ∃ e : Fin T.n ≃ Fin T'.n, IsRelabeling T T' e

/-- Equivalence is characterized by the existence of a data-preserving relabeling. -/
public theorem equivalent_iff_exists_relabeling (T T' : NumericalType) :
    Equivalent T T' ↔ ∃ e : Fin T.n ≃ Fin T'.n, IsRelabeling T T' e := Iff.rfl

/-- Every numerical type is equivalent to itself. -/
public theorem equivalent_refl (T : NumericalType) : Equivalent T T :=
  ⟨Equiv.refl (Fin T.n), IsRelabeling.refl T⟩

/-- Equivalence of numerical types is symmetric. -/
public theorem equivalent_symm {T T' : NumericalType} : Equivalent T T' → Equivalent T' T := by
  rintro ⟨e, h⟩
  refine ⟨e.symm, ?_⟩
  exact
    { multiplicity_eq := fun i => by
        simpa only [Equiv.apply_symm_apply] using (h.multiplicity_eq (e.symm i)).symm
      intersection_eq := fun i j => by
        simpa only [Equiv.apply_symm_apply] using
          (h.intersection_eq (e.symm i) (e.symm j)).symm
      weight_eq := fun i => by
        simpa only [Equiv.apply_symm_apply] using (h.weight_eq (e.symm i)).symm
      componentGenus_eq := fun i => by
        simpa only [Equiv.apply_symm_apply] using (h.componentGenus_eq (e.symm i)).symm }

/-- Equivalence of numerical types is transitive. -/
public theorem equivalent_trans {T T' T'' : NumericalType} :
    Equivalent T T' → Equivalent T' T'' → Equivalent T T'' := by
  rintro ⟨e, h⟩ ⟨e', h'⟩
  refine ⟨e.trans e', ?_⟩
  exact
    { multiplicity_eq := fun i => (h.multiplicity_eq i).trans (h'.multiplicity_eq (e i))
      intersection_eq := fun i j =>
        (h.intersection_eq i j).trans (h'.intersection_eq (e i) (e j))
      weight_eq := fun i => (h.weight_eq i).trans (h'.weight_eq (e i))
      componentGenus_eq := fun i => (h.componentGenus_eq i).trans (h'.componentGenus_eq (e i)) }

/-- The explicit setoid of numerical types modulo data-preserving relabeling. -/
public def setoid : Setoid NumericalType where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- The relation of `NumericalType.setoid` is equivalence under relabeling. -/
public theorem setoid_rel (T T' : NumericalType) : setoid.r T T' ↔ Equivalent T T' := Iff.rfl

end NumericalType
