/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient.FiniteProjective

/-!
# Alternating traces of bounded finite-projective cochain complexes

The signed sum of termwise traces is independent of the bounding interval
and is invariant under homotopy and homotopy retractions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex
open scoped Ring

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [Ring R]
variable {P : CochainComplex (ModuleCat R) ℤ} [hP : P.IsBoundedFiniteProjective]

/-- The alternating trace of an endomorphism of a bounded finite-projective
cochain complex, as an additive map into `R♮`. -/
noncomputable def traceNatural : (P ⟶ P) →+ R♮ :=
  let h := hP.bounded
  let a := h.choose
  let b := h.choose_spec.choose
  ∑ i ∈ Finset.Icc a b,
    Int.negOnePow i •
      (LinearMap.FiniteProjective.traceNatural.comp
        (ModuleCat.homAddEquiv.toAddMonoidHom.comp (Hom.fAddMonoidHom i)))

/-- The cochain trace is the signed sum of termwise finite-projective traces over
any bounding interval. -/
theorem traceNatural_eq_sum (f : P ⟶ P) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    traceNatural f =
      ∑ i ∈ Finset.Icc a b,
        Int.negOnePow i •
          LinearMap.FiniteProjective.traceNatural (ModuleCat.Hom.hom (f.f i)) := sorry

/-- Homotopic chain maps have the same alternating trace in `R♮`. -/
theorem traceNatural_homotopy {f g : P ⟶ P} (h_homotopy : Homotopy f g) :
    traceNatural f = traceNatural g := sorry

/-- If `γ2 ≫ γ1` is homotopic to `𝟙 P`, conjugating an endomorphism does not
change the alternating trace. -/
theorem traceNatural_conjugate {Q : CochainComplex (ModuleCat R) ℤ}
    [Q.IsBoundedFiniteProjective] (γ1 : Q ⟶ P) (γ2 : P ⟶ Q)
    (h_homotopy : Homotopy (γ2 ≫ γ1) (𝟙 P)) (f : P ⟶ P) :
    traceNatural (γ1 ≫ f ≫ γ2) = traceNatural f := sorry

end CochainComplex.IsBoundedFiniteProjective
