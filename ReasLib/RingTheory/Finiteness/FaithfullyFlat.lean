/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully Flat Base Change of Algebra Finiteness

This leaf packages the two bidirectional finiteness criteria for a faithfully
flat scalar extension. Mathlib provides base-change stability and descent as
separate results; the equivalences here are the reusable consumer interface.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FiniteType

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `00QP`: finite type is detected after faithfully flat scalar extension. -/
@[stacks 00QP "faithfully flat base change of finite type"]
theorem iff_tensorProduct_of_faithfullyFlat (R' : Type w)
    [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] :
    Algebra.FiniteType R S ↔ Algebra.FiniteType R' (R' ⊗[R] S) := sorry

end Algebra.FiniteType

namespace Algebra.FinitePresentation

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `00QQ`: finite presentation is detected after faithfully flat scalar extension. -/
@[stacks 00QQ "faithfully flat base change of finite presentation"]
theorem iff_tensorProduct_of_faithfullyFlat (R' : Type w)
    [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] :
    Algebra.FinitePresentation R S ↔
      Algebra.FinitePresentation R' (R' ⊗[R] S) := sorry

end Algebra.FinitePresentation
