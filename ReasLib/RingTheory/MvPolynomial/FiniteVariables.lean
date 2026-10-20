/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-variable models of multivariate polynomials

Finite families of multivariate polynomials descend to a polynomial ring in finitely many
variables. An injective renaming is the corresponding flat extension, and splitting a set of
variables from its complement gives an explicit algebra equivalence.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

variable {σ : Type u} {τ : Type v} {R : Type w}

/-- The explicit algebra equivalence which first adjoins the variables in `s` and then those in
its complement. -/
@[stacks 01BX "variable splitting"]
noncomputable def splitAlgEquiv [CommSemiring R] (s : Set σ) :
    MvPolynomial (sᶜ : Set σ) (MvPolynomial s R) ≃ₐ[R] MvPolynomial σ R :=
  (sumAlgEquiv R (sᶜ : Set σ) s).symm.trans
    (renameEquiv R ((Equiv.sumComm (sᶜ : Set σ) s).trans
      (@Equiv.Set.sumCompl σ s (Classical.decPred _))))

/-- The variable-splitting equivalence sends a coefficient polynomial to its canonical rename. -/
@[simp]
theorem splitAlgEquiv_C [CommSemiring R] (s : Set σ) (p : MvPolynomial s R) :
    splitAlgEquiv (R := R) s (C p) = rename Subtype.val p := sorry

/-- The variable-splitting equivalence sends a complementary variable to the corresponding
variable of the full polynomial ring. -/
@[simp]
theorem splitAlgEquiv_X [CommSemiring R] (s : Set σ) (i : (sᶜ : Set σ)) :
    splitAlgEquiv (R := R) s (X i) = X i.1 := sorry

/-- Every finite family of multivariate polynomials is obtained by renaming polynomials in one
common finite set of variables. -/
@[stacks 01BX "finite-variable support"]
theorem exists_finset_rename_family [CommSemiring R]
    {ι : Type*} [Finite ι] (p : ι → MvPolynomial σ R) :
    ∃ s : Finset σ, ∀ i, ∃ q : MvPolynomial s R,
      p i = rename Subtype.val q := sorry

/-- Renaming variables along an injection is a flat ring homomorphism. -/
@[stacks 01BX "flat variable inclusion"]
theorem rename_flat [CommRing R] (f : σ → τ) (hf : Function.Injective f) :
    (rename (R := R) f).toRingHom.Flat := sorry

end MvPolynomial

namespace Ideal.FG

variable {σ : Type u} {R : Type w} [CommSemiring R]

/-- A finitely generated ideal of a multivariate polynomial ring descends, with finite
generators, to a polynomial ring on a finite set of variables. -/
@[stacks 01BX "descent of finitely generated ideals"]
theorem exists_mvPolynomial_map_rename {I : Ideal (MvPolynomial σ R)} (hI : I.FG) :
    ∃ (s : Finset σ) (J : Ideal (MvPolynomial s R)),
      J.FG ∧ J.map (MvPolynomial.rename Subtype.val) = I := sorry

end Ideal.FG
