module

public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.Topology.Catenary
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.Topology.Specialization.Dimension

/-!
# Dimension of locally algebraic schemes over a field

This module relates topological and local-ring dimensions to residue-field
transcendence degrees for schemes locally of finite type over a field.
-/

@[expose] public section

open Specialization TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The transcendence degree over the base field of the residue field at a point. -/
noncomputable abbrev baseFieldTrdegAt (X : SchemeOverField k) (x : X.left) : ℕ :=
  Cardinal.toNat (Algebra.trdeg k (X.left.residueField x))

/-- The underlying space of a locally algebraic scheme over a field is catenary. -/
instance instCatenarySpaceOfLocallyAlgebraic
    (X : SchemeOverField k) [LocallyAlgebraic X] : CatenarySpace X.left := sorry

/-- At a closed point of a locally algebraic scheme over a field, local topological dimension
equals the Krull dimension of the stalk. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_of_isClosed
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left)
    (hx : IsClosed ({x} : Set X.left)) :
    topologicalKrullDimAt x = ringKrullDim (stalkRing X x) := sorry

/-- Every nonempty open of an irreducible locally algebraic scheme over a field has the same
topological Krull dimension as the whole scheme. -/
theorem topologicalKrullDim_open_eq_of_irreducible
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    (U : X.left.Opens) (hU : Set.Nonempty (U : Set X.left)) :
    topologicalKrullDim U = topologicalKrullDim X.left := sorry

/-- Every point of an irreducible locally algebraic scheme over a field has local dimension equal
to the global dimension. -/
theorem topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    (x : X.left) :
    topologicalKrullDim X.left = topologicalKrullDimAt x := sorry

/-- Every chain of irreducible closed subsets of an irreducible locally algebraic scheme over a
field extends to a maximal chain. -/
theorem exists_maxChain_irreducibleCloseds
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    (s : Set (IrreducibleCloseds X.left)) (hs : IsChain (· ≤ ·) s) :
    ∃ t : Set (IrreducibleCloseds X.left), IsMaxChain (· ≤ ·) t ∧ s ⊆ t := sorry

/-- Every maximal chain of irreducible closed subsets of an irreducible locally algebraic scheme
has cardinality one more than the topological Krull dimension. -/
theorem maxChainIrreducibleCloseds_encard
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    (s : Set (IrreducibleCloseds X.left)) (hs : IsMaxChain (· ≤ ·) s) :
    ((s.encard : ℕ∞) : WithBot ℕ∞) = topologicalKrullDim X.left + 1 := sorry

/-- The local dimension at a point of a locally algebraic scheme is the attained maximum of the
dimensions of the irreducible components containing that point. -/
theorem isGreatest_topologicalKrullDim_irreducibleComponents_through
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left) :
    IsGreatest
      {d : WithBot ℕ∞ |
        ∃ Z : irreducibleComponents X.left,
          x ∈ (Z : Set X.left) ∧ d = topologicalKrullDim Z}
      (topologicalKrullDimAt x) := sorry

/-- The local dimension at a point of a locally algebraic scheme is the attained minimum of the
Krull dimensions of stalks at its closed specializations. -/
theorem isLeast_ringKrullDim_stalk_closedSpecializations
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left) :
    IsLeast
      {d : WithBot ℕ∞ |
        ∃ x' : {x' : X.left // IsClosed ({x'} : Set X.left)},
          x ⤳ x' ∧ d = ringKrullDim (stalkRing X x')}
      (topologicalKrullDimAt x) := sorry

/-- On an irreducible locally algebraic scheme over a field, the global dimension is the
base-field transcendence degree at its generic point. -/
theorem topologicalKrullDim_eq_baseFieldTrdegAt_of_mem_genericPoints
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    (x : X.left) (hx : x ∈ genericPoints X.left) :
    topologicalKrullDim X.left = (baseFieldTrdegAt X x : WithBot ℕ∞) := sorry

/-- Base-field transcendence degree drops by exactly one along an immediate specialization in a
locally algebraic scheme. -/
theorem baseFieldTrdegAt_eq_add_one_of_immediateSpecialization
    (X : SchemeOverField k) [LocallyAlgebraic X] {x x' : X.left}
    (hxx' : IsImmediateSpecialization x x') :
    baseFieldTrdegAt X x = baseFieldTrdegAt X x' + 1 := sorry

/-- The global dimension of a locally algebraic scheme over a field is the indexed supremum of
the base-field transcendence degrees at the generic points of its irreducible components. -/
theorem topologicalKrullDim_eq_iSup_baseFieldTrdegAt_genericPoints
    (X : SchemeOverField k) [LocallyAlgebraic X] :
    topologicalKrullDim X.left =
      ⨆ η : genericPoints X.left, (baseFieldTrdegAt X η : WithBot ℕ∞) := sorry

/-- Local topological dimension is monotone along a nontrivial specialization in a locally
algebraic scheme over a field. -/
theorem topologicalKrullDimAt_le_of_nontrivialSpecialization
    (X : SchemeOverField k) [LocallyAlgebraic X] {x x' : X.left}
    (hxx' : x ⤳ x') (hneq : x ≠ x') :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt x' := sorry

/-- Krull dimension of stalks strictly increases along a nontrivial specialization in a locally
algebraic scheme over a field. -/
theorem ringKrullDim_stalk_lt_of_nontrivialSpecialization
    (X : SchemeOverField k) [LocallyAlgebraic X] {x x' : X.left}
    (hxx' : x ⤳ x') (hneq : x ≠ x') :
    ringKrullDim (stalkRing X x) < ringKrullDim (stalkRing X x') := sorry

/-- Base-field transcendence degree strictly decreases along a nontrivial specialization in a
locally algebraic scheme. -/
theorem baseFieldTrdegAt_gt_of_nontrivialSpecialization
    (X : SchemeOverField k) [LocallyAlgebraic X] {x x' : X.left}
    (hxx' : x ⤳ x') (hneq : x ≠ x') :
    baseFieldTrdegAt X x > baseFieldTrdegAt X x' := sorry

/-- A maximal chain in a specialization interval has cardinality equal to the difference of the
endpoint base-field transcendence degrees plus one. -/
theorem maxChainSpecializationInterval_encard
    (X : SchemeOverField k) [LocallyAlgebraic X] {x x' : X.left}
    (hxx' : x ⤳ x') (hneq : x ≠ x')
    (s : Set (Set.Icc (Specialization.toEquiv x') (Specialization.toEquiv x)))
    (hs : IsMaxChain (· ≤ ·) s) :
    s.encard = baseFieldTrdegAt X x - baseFieldTrdegAt X x' + 1 := sorry

/-- Local dimension is the sum of base-field transcendence degree and the Krull dimension of the
stalk for a locally algebraic scheme over a field. -/
theorem topologicalKrullDimAt_eq_baseFieldTrdegAt_add_ringKrullDim_stalk
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left) :
    topologicalKrullDimAt x =
      (baseFieldTrdegAt X x : WithBot ℕ∞) + ringKrullDim (stalkRing X x) := sorry

/-- Along an immediate specialization in an irreducible locally algebraic scheme over a field,
the Krull dimension of the stalk increases by one. -/
theorem ringKrullDim_stalk_eq_add_one_of_immediateSpecialization_of_irreducible
    (X : SchemeOverField k) [LocallyAlgebraic X] [IrreducibleSpace X.left]
    {x x' : X.left} (hxx' : IsImmediateSpecialization x x') :
    ringKrullDim (stalkRing X x') = ringKrullDim (stalkRing X x) + 1 := sorry

/-- Along an immediate specialization in an equidimensional locally algebraic scheme over a
field, the Krull dimension of the stalk increases by one. -/
theorem ringKrullDim_stalk_succ_of_equidimensional
    (X : SchemeOverField k) [LocallyAlgebraic X]
    [TopologicalSpace.EquidimensionalSpace X.left]
    {x x' : X.left} (hxx' : IsImmediateSpecialization x x') :
    ringKrullDim (stalkRing X x') = ringKrullDim (stalkRing X x) + 1 := sorry

end AlgebraicGeometry.SchemeOverField
