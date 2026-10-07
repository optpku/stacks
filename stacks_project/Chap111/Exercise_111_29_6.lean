module

public import ReasLib.RingTheory.Polynomial.FrobeniusSpecialization
public import ReasLib.RingTheory.Polynomial.FrobeniusNorm
public import ReasLib.RingTheory.MvPolynomial.FrobeniusGraph
import StacksCheckRecall

/-!
# Exercise 111.29.6: questions, not asserted answers

The source calls these unsolved problems. Only (1) includes an affirmative hint.
The literal proposition asked in (2) is named without asserting it. Its bare norm
divisibility condition permits the unit witness; no degree-matching condition is
silently added. In (3) the source specifies the input but only calls the conclusion
analogous. Only that input predicate is checked below. The open conclusion is retained in
the documentation and item contract, without a predicate parameter, plane norm
construction, or affirmative answer.
-/

open scoped Polynomial.Bivariate

/- Exercise 111.29.6 (1): the existence question has an affirmative hint for
`Polynomial.ySubXSucc = Y - C (X + 1)` and
`Polynomial.ySqSubXSqAddOne = Y ^ 2 - C (X ^ 2) + 1`.
Their separate infinite-irreducibility assertions live in the specialization owner. -/
@[stacks 02ET] #check (Polynomial.exists_intEvalXPowMod_irreducible_infinite :
  ∃ f : ℤ[X][Y],
    {p : ℕ | p.Prime ∧ Irreducible (Polynomial.intEvalXPowMod p f)}.Infinite)

/- Exercise 111.29.6 (2): does an eventual split-degree factorization imply an
eventual norm divisor from one fixed monic positive-degree relation and polynomial?
This check names a proposition without asserting its truth. Literal norm
divisibility permits `g = 1` and does not specify a nontrivial explanation.
`Polynomial.natDegree_intEvalXPowMod` supplies the eventual degree formula. -/
@[stacks 02ET] #check (Polynomial.FrobeniusNorm.splitFactorizationImpliesNormDivisor : Prop)

/- Exercise 111.29.6 (3): the analogous norm-explanation question is posed for
an irreducible integer polynomial in four variables whose plane Frobenius-graph
specializations factor for all sufficiently large primes. The checked predicate
formalizes only this specified input, not an answer or the full analogous
conclusion: the two-variable finite algebra, structure map, and norm are unspecified. -/
@[stacks 02ET] #check (MvPolynomial.FrobeniusGraph.eventualPlaneFactorization :
  MvPolynomial MvPolynomial.FrobeniusGraph.Coord ℤ → Prop)
