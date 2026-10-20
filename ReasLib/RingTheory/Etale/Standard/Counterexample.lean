/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A composition counterexample for standard etale algebras

Standard etale algebras are stable under base change and principal
localization, but not under composition.  This leaf owns the reusable
existential counterexample.

@stack 00UC
-/

@[expose] public section

universe u v w

namespace Algebra.IsStandardEtale

/-- Lemma 10.144.2 (4): there is a tower of standard etale maps whose
composite is not standard etale. -/
@[stacks 00UC "(4), composition counterexample"]
theorem exists_tower_with_nonstandard_composite :
    ∃ (R : Type u) (S : Type v) (T : Type w)
      (_ : CommRing R) (_ : CommRing S) (_ : CommRing T)
      (_ : Algebra R S) (_ : Algebra S T) (_ : Algebra R T) (_ : IsScalarTower R S T),
      Algebra.IsStandardEtale R S ∧ Algebra.IsStandardEtale S T ∧
        ¬ Algebra.IsStandardEtale R T := sorry

end Algebra.IsStandardEtale
