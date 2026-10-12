/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import stacks_project.Chap60.Remark_60_6_7_Forms

@[expose] public section

universe u v

/- Remark 60.6.7: for a ring map `f : A →+* B` and divided powers `δ` on `J`, the
quotient of `Ω[B⁄A]` by the divided-power relations carries a de Rham differential family. -/
@[stacks 07HZ] #check (KaehlerDifferential.DeRham.existsDividedPowerFamily :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) {J : Ideal B} (δ : DividedPowers J),
    -- Local instance justification (instance diamond): f.toAlgebra is scoped locally to avoid competing Algebra A B instances derived from unrelated ring-hom choices.
    letI : Algebra A B := f.toAlgebra
    ∃ dδ : DifferentialOperator.DeRham.Family A B
        (KaehlerDifferential.DeRham.dividedPowerDifferential f δ),
      DifferentialOperator.DeRham.IsDifferential
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation f δ) dδ)
