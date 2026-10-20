/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.MvPolynomial
public import ReasLib.RingTheory.MvPolynomial.Noetherian
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import StacksCheckRecall

@[expose] public section

/- Exercise 111.1.2 (1): the polynomial ring `MvPolynomial ℕ+ ℤ` in countably many
variables is coherent, i.e. every finitely generated ideal is finitely presented as an
`R`-module (`Module.FinitePresentation`). -/
@[stacks 02CH]
#check (MvPolynomial.isCoherentRing_of_noetherian (σ := ℕ+) (R := ℤ) :
  IsCoherentRing (MvPolynomial ℕ+ ℤ))

/- Exercise 111.1.2 (2): the same ring `MvPolynomial ℕ+ ℤ` is not Noetherian. -/
@[stacks 02CH]
#check (MvPolynomial.not_isNoetherianRing_of_infinite (σ := ℕ+) (R := ℤ) :
  ¬ IsNoetherianRing (MvPolynomial ℕ+ ℤ))
