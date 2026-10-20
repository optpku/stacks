/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Projective.Characterizations
import StacksCheckRecall

/-!
# Definition 10.77.1

Projectivity is already represented by `Module.Projective`; the exactness of
`Hom_R(P, -)` is its reusable characterization rather than a new chapter-local
definition.

@stack 05CE
-/

@[expose] public section

/- Definition 10.77.1 (Tag 05CE): the module-theoretic projectivity
criterion is the reusable `Module.Projective.iff_exact_hom` bridge over the
generic categorical projectivity criterion. -/
@[stacks 05CE]
#check @Module.Projective.iff_exact_hom
