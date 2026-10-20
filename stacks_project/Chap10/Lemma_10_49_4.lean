/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Integral
import StacksCheckRecall

@[expose] public section

/-!
# Tensor Products with Geometrically Integral Algebras

@stack 09P9

Lemma 10.49.4 is a canonical recall of the shared tensor-domain theorem for a
geometrically integral affine algebra over a field.
-/

/- Lemma 10.49.4 (Tag 09P9): tensoring an integral-domain `k`-algebra with a geometrically
integral affine `k`-algebra produces an integral domain. -/
@[stacks 09P9 "tensor-product domain criterion"]
#check @AlgebraicGeometry.SchemeOverField.isDomain_tensorProduct_of_geometricallyIntegral_right
