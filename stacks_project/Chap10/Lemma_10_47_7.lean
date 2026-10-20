/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Irreducible
import StacksCheckRecall

@[expose] public section

/-!
# Geometric Irreducibility After Affine Base Change
@stack 037O

Lemma 10.47.7 is a canonical recall of the affine tensor-product base-change
theorem and its corresponding geometric-irreducibility instance.
-/

/- Lemma 10.47.7 (Tag 037O): if `S` is geometrically irreducible over a field `k`, then the
projection `Spec (R ⊗[k] S) ⟶ Spec R` induces an equivalence on irreducible components. -/
@[stacks 037O "irreducible-components equivalence"]
#check @AlgebraicGeometry.SchemeOverField.irreducibleComponentsEquiv_tensorProduct_projection

@[stacks 037O "geometric irreducibility"]
#check @AlgebraicGeometry.SchemeOverField.geometricallyIrreducible_tensorProduct_projection

@[stacks 037O "geometric irreducibility instance"]
#check @AlgebraicGeometry.SchemeOverField.instGeometricallyIrreducible_tensorProduct_projection
