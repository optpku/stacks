/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Extension.Cotangent.Basis

@[expose] public section

/-!
# Free Cotangent Presentation Recall

The source statement is exactly the finite-presentation theorem owned by
`Algebra.Generators`; no chapter-specific wrapper is needed.

@stack 07CF
-/

/- Lemma 10.136.6, tag `07CF`: if `S` is a finitely presented `R`-algebra with a finite polynomial
presentation whose conormal module `I / I²` is free over `S`, then `S` admits another finite
presentation whose conormal module is free with basis given by the classes of the defining
relations. In mathlib this is exactly
`Algebra.Generators.exists_presentation_of_free_cotangent`. -/
@[stacks 07CF "finite presentations with free cotangent admit a basis presentation"]
#check @Algebra.Generators.exists_presentation_of_free_cotangent
