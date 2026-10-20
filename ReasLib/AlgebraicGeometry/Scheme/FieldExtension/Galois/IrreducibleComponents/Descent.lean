module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Subalgebra
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.FixedPoints

/-!
# Galois-orbit descent of irreducible components

This leaf records the finite-orbit form of the algebraic-closure component descent theorem.  The
orbit is part of the statement, rather than an auxiliary finite set whose elements are merely
pairwise related, so the invariant closed subset is recoverable by downstream code.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Irreducible.Descent

/-- The opposite-Galois action on irreducible components, transported to the same carrier
equipped with the discrete topology. -/
noncomputable instance instOppositeMulActionWithDiscreteTopology
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction (Gal(kbar/k))ᵐᵒᵖ
      (WithDiscreteTopology (irreducibleComponents (FieldExtension.baseChange k kbar f))) :=
  (WithTopology.equiv
    (irreducibleComponents (FieldExtension.baseChange k kbar f)) ⊥).mulAction
      (Gal(kbar/k))ᵐᵒᵖ

/-- The opposite-Galois action on the irreducible components after base change to an
algebraic closure is continuous when the component set has the discrete topology. -/
instance instContinuousSMulAlgebraicClosure
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    ContinuousSMul (Gal(kbar/k))ᵐᵒᵖ
      (WithDiscreteTopology
        (irreducibleComponents (FieldExtension.baseChange k kbar f))) := sorry

/-- Every irreducible component after base change to an algebraic closure descends from an
irreducible component over a finite intermediate field. -/
theorem exists_finiteSubextension_preimage_eq
    (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (Tbar : irreducibleComponents (FieldExtension.baseChange k kbar f)) :
    ∃ K : IntermediateField k kbar, FiniteDimensional k K ∧
      ∃ T : irreducibleComponents (FieldExtension.baseChange k K f),
        (Scheme.AffineBaseChange.Subalgebra.map f K.toSubalgebra) ⁻¹'
            (T : Set (FieldExtension.baseChange k K f)) =
          (Tbar : Set (FieldExtension.baseChange k kbar f)) := sorry

/-- The irreducible components above a base component form one finite Galois orbit after an
algebraic-closure base change. -/
theorem preimage_eq_iUnion_orbit
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (T : irreducibleComponents X) :
    ∃ Tbar : irreducibleComponents (FieldExtension.baseChange k kbar f),
      (MulAction.orbit (Gal(kbar/k))ᵐᵒᵖ Tbar).Finite ∧
        (FieldExtension.toSource k kbar f).base ⁻¹' (T : Set X) =
          ⋃ Z ∈ MulAction.orbit (Gal(kbar/k))ᵐᵒᵖ Tbar,
            (Z : Set (FieldExtension.baseChange k kbar f)) := sorry

end FieldExtension.Galois.Irreducible.Descent

end AlgebraicGeometry
