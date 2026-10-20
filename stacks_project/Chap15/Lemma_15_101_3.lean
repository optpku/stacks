/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.QuotientComplex

/-!
# Lemma 15.101.3

@stack 0G9M
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.IdealPower.QuotientComplex
open Opposite

universe u

/- Lemma 15.101.3 (0G9M): for a Noetherian ring `A`, an ideal `I`, and a bounded
complex `M` of finite `A`-modules, the canonical comparison from the derived
ideal-power tensor system to the termwise quotient-complex system is an
isomorphism after passing to sequential pro-objects.  The reusable systems and
comparison are owned by `ReasLib`; this chapter file is intentionally boundary-only.

The sequential facade is indexed by `n : ℕ` with stage `n` representing the
textbook quotient by `I ^ (n + 1)`, and the source is presented directly in the
textbook order `M ⊗ᴸ_A (A ⧸ I ^ (n + 1))`. -/
@[stacks 0G9M "derived tensor comparison with ideal-power quotient complexes"]
#check @comparison_isIso

/- Keep the source hypotheses visible at the chapter boundary.  In particular,
the boundedness and finiteness assumptions belong to the comparison theorem;
they are not hidden in a local instance or a chapter-specific wrapper. -/
#check fun {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) ↦
  comparison_isIso
    (I := I) (M := M) hboundedBelow hboundedAbove hfinite

/- The source-facing systems are exposed separately so downstream chapters can
reuse their stages and transitions without importing this chapter. -/
#check @stage
#check @step
#check @system
#check @standardSystem
#check @comparison
#check @CategoryTheory.Pro.SequentialHom.ofNatTrans
#check @CategoryTheory.Pro.SequentialHom.toHom
