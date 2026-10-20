/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral.Criteria
import StacksCheckRecall

@[expose] public section

/-!
# Field tests for geometric integrality

@stack 0FWF

Lemma 10.49.3 (Tag 0FWF) is a direct recall of the reusable affine
geometric-integrality criteria. Its three source clauses are represented by
the two atomic shared equivalences, with the common left side understood once.
-/

@[stacks 0FWF "finite-extension criterion"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIntegral.iff_isDomain_finiteExtension

@[stacks 0FWF "algebraic-closure criterion"]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIntegral.iff_isDomain_algebraicClosure
