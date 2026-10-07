module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A regular sequence whose second term is a zerodivisor

@stack 00LH

The presentation data in the source is explicit: the infinitely generated
polynomial ring, both relation families, the quotient ring, and the maximal
ideal used for the local example are all named below.
-/

@[expose] public section

open scoped nonZeroDivisors

noncomputable section

namespace Algebra.Example_10_68_3

universe u

variable (k : Type u) [Field k]

/-- Variables `x`, `y`, and `w_i` in the presentation of Example 10.68.3. -/
inductive Variable
  | x
  | y
  | w : ℕ → Variable
  deriving DecidableEq

/-- The ambient polynomial ring `k[x,y,w_0,w_1,...]`. -/
abbrev PolynomialRing : Type u := MvPolynomial Variable k

/-- The relation `y w_i` in the presentation. -/
def yMulW (i : ℕ) : PolynomialRing k :=
  MvPolynomial.X Variable.y * MvPolynomial.X (Variable.w i)

/-- The relation `w_i - x w_(i+1)` in the presentation. -/
def wRecurrence (i : ℕ) : PolynomialRing k :=
  MvPolynomial.X (Variable.w i) -
    MvPolynomial.X Variable.x * MvPolynomial.X (Variable.w (i + 1))

/-- The two infinite families of defining relations. -/
def relations : Set (PolynomialRing k) :=
  Set.range (yMulW k) ∪ Set.range (wRecurrence k)

/-- The defining ideal `(y w_i, w_i - x w_(i+1) | i ≥ 0)`. -/
def ideal : Ideal (PolynomialRing k) := Ideal.span (relations k)

/-- The quotient ring in Example 10.68.3. -/
abbrev Ring : Type u := PolynomialRing k ⧸ ideal k

/-- The class of `x` in the quotient ring. -/
def x : Ring k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X Variable.x)

/-- The class of `y` in the quotient ring. -/
def y : Ring k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X Variable.y)

/-- The class of `w_i` in the quotient ring. -/
def w (i : ℕ) : Ring k :=
  Ideal.Quotient.mk (ideal k) (MvPolynomial.X (Variable.w i))

/-- The ideal `(x,y,w_i | i ≥ 0)` used for the local example. -/
def maximalIdeal : Ideal (Ring k) :=
  Ideal.span (Set.insert (x k) (Set.insert (y k) (Set.range (w k))))

/-- The displayed ideal `(x,y,w_i)` is maximal. -/
theorem maximalIdeal_isMaximal : (maximalIdeal k).IsMaximal := sorry

/-- The closed point determined by `(x,y,w_i)`. -/
def closedPoint : MaximalSpectrum (Ring k) :=
  ⟨maximalIdeal k, maximalIdeal_isMaximal k⟩

/-- The prime-spectrum view of the distinguished closed point. -/
abbrev prime : PrimeSpectrum (Ring k) := (closedPoint k).toPrimeSpectrum

/-- The local ring at the distinguished closed point. -/
abbrev LocalRing : Type u := Localization.AtPrime (prime k).asIdeal

/-- The image of `x` in the local ring. -/
def localizedX : LocalRing k := algebraMap (Ring k) (LocalRing k) (x k)

/-- The image of `y` in the local ring. -/
def localizedY : LocalRing k := algebraMap (Ring k) (LocalRing k) (y k)

/-- Example 10.68.3 (1): in the displayed quotient ring, `x,y` is a regular
sequence although `y` is a zerodivisor. -/
@[stacks 00LH "(1)"]
theorem regularSequence_and_y_zeroDivisor :
    RingTheory.Sequence.IsRegular (M := Ring k) [x k, y k] ∧
      y k ∉ nonZeroDivisors (Ring k) := sorry

/-- Example 10.68.3 (2): localizing at `(x,y,w_i)` preserves both the regular
sequence `x,y` and the fact that `y` is a zerodivisor. -/
@[stacks 00LH "(2)"]
theorem localized_regularSequence_and_y_zeroDivisor :
    RingTheory.Sequence.IsRegular (M := LocalRing k) [localizedX k, localizedY k] ∧
      localizedY k ∉ nonZeroDivisors (LocalRing k) := sorry

#check @MaximalSpectrum.toPrimeSpectrum
#check @Algebra.Example_10_68_3.closedPoint

#print axioms Algebra.Example_10_68_3.relations
#print axioms Algebra.Example_10_68_3.ideal
#print axioms Algebra.Example_10_68_3.closedPoint

end Algebra.Example_10_68_3
