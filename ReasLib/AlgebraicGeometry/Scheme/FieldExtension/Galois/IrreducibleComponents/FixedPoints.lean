/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Closeds.Descent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

/-!
# Fixed irreducible components under a Galois action

This module characterizes the irreducible components fixed by the opposite-Galois action on a
separable-closure base change.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Irreducible

/-- An irreducible component after base change to a separable closure is fixed by the
opposite-Galois action exactly when it is the pullback of a geometrically irreducible component
over the base field. -/
theorem mem_fixedPoints_iff_exists_geometricallyIrreducibleComponent
    (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : irreducibleComponents (FieldExtension.baseChange k ksep f)) :
    Tbar ∈ MulAction.fixedPoints (Gal(ksep/k))ᵐᵒᵖ
        (irreducibleComponents (FieldExtension.baseChange k ksep f)) ↔
      ∃ T : irreducibleComponents X,
        GeometricallyIrreducible (X.irreducibleComponentSubschemeι T ≫ f) ∧
          FieldExtension.Galois.Closeds.preimage k ksep f
              (X.irreducibleComponentClosed T) =
            (FieldExtension.baseChange k ksep f).irreducibleComponentClosed Tbar := sorry

end FieldExtension.Galois.Irreducible

end AlgebraicGeometry
