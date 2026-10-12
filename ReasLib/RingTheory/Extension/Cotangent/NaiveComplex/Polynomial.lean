/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical

/-!
# Naive Cotangent Complexes of Isomorphic Presentations

@stack 08Q1

This leaf records the presentation-level collapse of the naive cotangent
complex when the presentation ring already maps isomorphically to the target,
and its canonical polynomial-algebra specialization.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Algebra.Extension.NaiveCotangent.Bijective

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The conormal module of a presentation is subsingleton when its structural algebra map is
bijective. -/
@[stacks 08Q1 "isomorphic presentation"]
theorem cotangentSubsingleton
    (P : Extension.{w} R S) (hP : Function.Bijective (algebraMap P.Ring S)) :
    Subsingleton P.Cotangent := sorry

/-- The map from a presentation's cotangent space to Kahler differentials is bijective when the
structural algebra map of the presentation is bijective. -/
@[stacks 08Q1 "isomorphic presentation"]
theorem toKaehlerBijective
    (P : Extension.{w} R S) (hP : Function.Bijective (algebraMap P.Ring S)) :
    Function.Bijective P.toKaehler := sorry

/-- A presentation with bijective structural algebra map has naive cotangent complex homotopy
equivalent to the universe-lifted single complex on `Ω[S⁄R]` in degree zero.  The lift is needed
because the presentation generators may live above the universes of `R` and `S`. -/
@[stacks 08Q1 "isomorphic presentation"]
theorem homotopyEquivSingleZero
    {ι : Type w} (P : Algebra.Generators R S ι)
    (hP : Function.Bijective (algebraMap P.Ring S)) :
    Nonempty <|
      HomotopyEquiv (complex P.toExtension)
        ((ChainComplex.single₀ (ModuleCat.{max u v w} S)).obj
          (ModuleCat.of.{max u v w} S (ULift.{max u w, v} Ω[S⁄R]))) := sorry

end Algebra.Extension.NaiveCotangent.Bijective

namespace Algebra.NaiveCotangent.Polynomial

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.134.3, tag `08Q1`: the canonical naive cotangent complex of a polynomial
`R`-algebra `S` is homotopy equivalent to the single complex on `Ω[S⁄R]` in degree zero. -/
@[stacks 08Q1 "polynomial algebra"]
theorem homotopyEquivSingleZero
    {ι : Type u} (e : MvPolynomial ι R ≃ₐ[R] S) :
    Nonempty <|
      HomotopyEquiv (Algebra.naiveCotangent R S)
        ((ChainComplex.single₀ (ModuleCat.{u} S)).obj (ModuleCat.of.{u} S Ω[S⁄R])) := sorry

end Algebra.NaiveCotangent.Polynomial
