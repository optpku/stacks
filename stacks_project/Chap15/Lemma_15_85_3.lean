/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Representative
import StacksCheckRecall

/-!
# Two-term representatives

This file is the source-facing recall for Lemma 15.85.3.

@stack 0G9E
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.85.3 (1): a derived module concentrated in degrees `-1` and `0` has a two-term
representative with free degree-zero term. -/
@[stacks 0G9E "Lemma 15.85.3 (1)"]
#check fun {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R))
    (hGE : K.IsGE (-1)) (hLE : K.IsLE 0) =>
  (IsTwoTermRepresentative.exists_free K hGE hLE :
    ∃ P : CochainComplex (ModuleCat R) ℤ,
      IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0))

/- Lemma 15.85.3 (2): under the Noetherian and finite-cohomology hypotheses, the representative
can be chosen finite in both terms and finite free in degree zero. -/
@[stacks 0G9E "Lemma 15.85.3 (2)"]
#check fun {R : Type u} [Ring R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R)) (hGE : K.IsGE (-1)) (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) =>
  (IsTwoTermRepresentative.exists_finiteFree K hGE hLE hHneg1 hH0 :
    ∃ P : CochainComplex (ModuleCat R) ℤ,
      IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) ∧
        Module.Finite R (P.X 0) ∧ Module.Finite R (P.X (-1)))

@[stacks 0G9E "two-term representative predicate"]
#check fun {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R))
    (P : CochainComplex (ModuleCat R) ℤ) =>
  (IsTwoTermRepresentative K P : Prop)
