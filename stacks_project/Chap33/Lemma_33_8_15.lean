/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.8.15 (1): the opposite-Galois action on geometric irreducible components is
continuous when the component set has the discrete topology. -/
@[stacks 04KZ] #check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.Descent.instContinuousSMulAlgebraicClosure :
    ∀ (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      ContinuousSMul (Gal(kbar/k))ᵐᵒᵖ
        (WithDiscreteTopology
          (irreducibleComponents (FieldExtension.baseChange k kbar f))))

/- Lemma 33.8.15 (2): every geometric irreducible component descends from an irreducible
component over a finite intermediate extension. -/
@[stacks 04KZ] #check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.Descent.exists_finiteSubextension_preimage_eq :
    ∀ (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (Tbar : irreducibleComponents (FieldExtension.baseChange k kbar f)),
      ∃ K : IntermediateField k kbar, FiniteDimensional k K ∧
        ∃ T : irreducibleComponents (FieldExtension.baseChange k K f),
          (Scheme.AffineBaseChange.Subalgebra.map f K.toSubalgebra) ⁻¹'
              (T : Set (FieldExtension.baseChange k K f)) =
            (Tbar : Set (FieldExtension.baseChange k kbar f)))

/- Lemma 33.8.15 (3): the geometric irreducible components above each irreducible component
form one finite opposite-Galois orbit whose union is its inverse image. -/
@[stacks 04KZ] #check
  (AlgebraicGeometry.FieldExtension.Galois.Irreducible.Descent.preimage_eq_iUnion_orbit :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (T : irreducibleComponents X),
      ∃ Tbar : irreducibleComponents (FieldExtension.baseChange k kbar f),
        (MulAction.orbit (Gal(kbar/k))ᵐᵒᵖ Tbar).Finite ∧
          (FieldExtension.toSource k kbar f).base ⁻¹' (T : Set X) =
            ⋃ Z ∈ MulAction.orbit (Gal(kbar/k))ᵐᵒᵖ Tbar,
              (Z : Set (FieldExtension.baseChange k kbar f)))
