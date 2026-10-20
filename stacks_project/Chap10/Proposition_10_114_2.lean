/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GlobalDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import ReasLib.RingTheory.KrullDimension.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Regularity and Global Dimension of Polynomial Algebras

@stack 00OQ

The polynomial-ring regularity, local-dimension, and global-dimension interfaces are retained at
their canonical typeclass/theorem layer.
-/

universe u

section

variable {k : Type u} [Field k]
variable {n : ℕ}

-- Local declaration justification (source-local notation): `A` is the source polynomial algebra
-- used uniformly by the three source-facing clauses below.
local notation "A" => MvPolynomial (Fin n) k

/- Proposition 10.114.2 (1) (Stacks tag `00OQ`): a polynomial algebra in
finitely many variables over a field is regular. -/
@[stacks 00OQ "(1)"]
#check @MvPolynomial.isRegularRing_of_isRegularRing

/-- The polynomial algebra in `n` variables over a field has finite global dimension. -/
@[stacks 00OQ "finite global dimension companion"]
instance isFiniteGlobalDimensionRing_mvPolynomial : IsFiniteGlobalDimensionRing A := sorry

/-- Proposition 10.114.2 (2) (Stacks tag `00OQ`): the global dimension of a
polynomial algebra in `n` variables over a field is `n`. -/
@[stacks 00OQ "(2)"]
theorem globalDimension_mvPolynomial_eq : globalDimension A = n := sorry

variable (m : MaximalSpectrum A)

/- Proposition 10.114.2 (3) (Stacks tag `00OQ`), regularity part: every
maximal localization is a regular local ring. -/
@[stacks 00OQ "(3), regularity"]
#check (inferInstance : IsRegularLocalRing (Localization.AtPrime m.asIdeal))

/- Proposition 10.114.2 (3), dimension part: every maximal localization has
dimension `n`. -/
@[stacks 00OQ "(3), dimension"]
#check MvPolynomial.ringKrullDim_localizationAtMaximal m

end
end
