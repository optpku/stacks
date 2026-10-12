/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.Target
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Residue fields of maps to a field target

For an object over a field target, its structural map factors canonically
through the residue field at its kernel.  This leaf owns that factorization,
the analogous factorization of the base-to-target map, and their compatibility.
It does not assume that the object is etale or localized.

@stack 04GW
-/

universe u v

namespace CommAlgCat.Over.Target.ResidueField

variable {R : Type u} {T : Type v} [CommRing R] [Field T] [Algebra R T]

/-- The structural map of an over-object to a field target, factored through
the residue field at its kernel. -/
@[stacks 04GW "residue-field factorization of an over-object target map"]
noncomputable abbrev map
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    (CommAlgCat.Over.Target.kernel A).ResidueField →+* T :=
  Ideal.ResidueField.lift (CommAlgCat.Over.Target.kernel A)
    (CommAlgCat.Over.Target.map A) le_rfl
    (Ideal.primeCompl_le_isUnit_comap_of_ker_eq
      (CommAlgCat.Over.Target.kernel A) (CommAlgCat.Over.Target.map A) rfl)

/-- The residue-field factorization recovers the structural target map on the
underlying ring. -/
@[stacks 04GW "structural map through the target-kernel residue field"]
theorem map_comp_algebraMap
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    (map A).comp (algebraMap A.left (CommAlgCat.Over.Target.kernel A).ResidueField) =
      CommAlgCat.Over.Target.map A := sorry

/-- The base-to-target map, factored through the residue field at its kernel. -/
@[stacks 04GW "residue-field factorization of a base target map"]
noncomputable abbrev baseMap {p : Ideal R} [p.IsPrime]
    (hbase : RingHom.ker (algebraMap R T) = p) :
    p.ResidueField →+* T :=
  Ideal.ResidueField.lift p (algebraMap R T) hbase.symm.le
    (Ideal.primeCompl_le_isUnit_comap_of_ker_eq p (algebraMap R T) hbase)

/-- The base residue-field factorization recovers the fixed algebra map to the target. -/
@[stacks 04GW "base target map through its residue field"]
theorem baseMap_comp_algebraMap {p : Ideal R} [p.IsPrime]
    (hbase : RingHom.ker (algebraMap R T) = p) :
    (baseMap hbase).comp (algebraMap R p.ResidueField) = algebraMap R T := sorry

/-- Factoring first through the base residue field and then through an
over-object gives its direct target residue-field factorization. -/
@[stacks 04GW "base compatibility of over-object target residue maps"]
theorem map_comp_base {p : Ideal R} [p.IsPrime]
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CategoryTheory.Over (CommAlgCat.of R T)) :
    (map A).comp
        (Ideal.ResidueField.map p (CommAlgCat.Over.Target.kernel A)
          (algebraMap R A.left) (CommAlgCat.Over.Target.baseComap hbase A)) =
      baseMap hbase := sorry

/-- When the target already carries a compatible `κ(p)`-algebra structure,
the canonical base residue-field factorization is its algebra map. -/
@[stacks 04GW "canonical base residue map as an algebra map"]
theorem baseMap_eq_algebraMap {p : Ideal R} [p.IsPrime]
    [Algebra p.ResidueField T] [IsScalarTower R p.ResidueField T]
    (hbase : RingHom.ker (algebraMap R T) = p) :
    baseMap hbase = algebraMap p.ResidueField T := sorry

end CommAlgCat.Over.Target.ResidueField
