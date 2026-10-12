/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Finite

universe u

namespace CommAlgCat.FiniteEtale

@[expose] public section

/-- The category of finite étale algebras over a separably closed field is anti-equivalent to finite types. -/
noncomputable def equivToFintypeOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale Ω)ᵒᵖ ≌ FintypeCat :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed Ω

end

end CommAlgCat.FiniteEtale
