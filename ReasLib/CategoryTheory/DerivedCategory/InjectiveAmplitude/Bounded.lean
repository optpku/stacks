/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Devissage
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Retracts
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Single
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite injective dimension from bounded data

Finite injective dimension can be assembled either from the finitely many cohomology objects of a
bounded derived object or from the terms of a bounded representative.  These statements are
formulated for any abelian category with enough injectives; module categories are immediate
specializations.

@stack 0A5V
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable [HasDerivedCategory.{w} C]

/-- Explicit bounded-cohomology form: a common injective-dimension bound `m` on cohomology
supported in `[c, d]` gives injective amplitude in `[c, d + m]`. -/
@[stacks 0A5V "(1), uniform cohomology bound"]
theorem HasInjectiveAmplitudeIn.ofBoundedHomology
    (K : DerivedCategory C) (c d : ℤ) (m : ℕ)
    (hGE : K.IsGE c) (hLE : K.IsLE d)
    (hH : ∀ i : ℤ, c ≤ i → i ≤ d →
      injectiveDimension ((DerivedCategory.homologyFunctor C i).obj K) ≤ m) :
    HasInjectiveAmplitudeIn K c (d + (m : ℤ)) := sorry

/-- Explicit bounded-representative form: a common injective-dimension bound `m` on the terms of
a complex supported in `[c, d]` gives amplitude `[c, d + m]` for its derived image. -/
@[stacks 0A5V "(2), uniform term bound"]
theorem HasInjectiveAmplitudeIn.ofBoundedTerms
    (K : CochainComplex C ℤ) (c d : ℤ) (m : ℕ)
    (hGE : K.IsStrictlyGE c) (hLE : K.IsStrictlyLE d)
    (hterm : ∀ i : ℤ, c ≤ i → i ≤ d → injectiveDimension (K.X i) ≤ m) :
    HasInjectiveAmplitudeIn (DerivedCategory.Q.obj K) c (d + (m : ℤ)) := sorry

/-- A common injective-dimension bound on a bounded representative gives the corresponding
injective-amplitude interval on the represented derived object. -/
@[stacks 0A5V "(2), represented uniform term bound"]
theorem HasInjectiveAmplitudeIn.ofBoundedRepresentative
    {L : DerivedCategory C} (K : CochainComplex C ℤ)
    (e : DerivedCategory.Q.obj K ≅ L) (c d : ℤ) (m : ℕ)
    (hGE : K.IsStrictlyGE c) (hLE : K.IsStrictlyLE d)
    (hterm : ∀ i : ℤ, c ≤ i → i ≤ d → injectiveDimension (K.X i) ≤ m) :
    HasInjectiveAmplitudeIn L c (d + (m : ℤ)) := sorry

/-- Lemma 15.70.5 (1), abstract form: a bounded derived object whose cohomology objects all have
finite injective dimension has finite injective dimension. -/
@[stacks 0A5V "(1), abstract bounded-derived form"]
theorem HasFiniteInjectiveDimension.ofBoundedHomology
    (K : DerivedCategory.Bounded C)
    (hH : ∀ i : ℤ,
      injectiveDimension ((DerivedCategory.Bounded.homologyFunctor C i).obj K) ≠ ⊤) :
    HasFiniteInjectiveDimension K.obj := sorry

/-- Lemma 15.70.5 (2), abstract form: a bounded cochain complex whose terms all have finite
injective dimension represents a derived object of finite injective dimension. -/
@[stacks 0A5V "(2), abstract bounded-complex form"]
theorem HasFiniteInjectiveDimension.ofBoundedTerms
    (K : CochainComplex.Bounded C)
    (hterm : ∀ i : ℤ, injectiveDimension (K.obj.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension (DerivedCategory.Q.obj K.obj) := sorry

/-- A derived object represented by a bounded complex whose terms all have finite injective
dimension has finite injective dimension. -/
@[stacks 0A5V "(2), represented bounded-complex form"]
theorem HasFiniteInjectiveDimension.ofBoundedRepresentative
    {L : DerivedCategory C} (K : CochainComplex.Bounded C)
    (e : DerivedCategory.Q.obj K.obj ≅ L)
    (hterm : ∀ i : ℤ, injectiveDimension (K.obj.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension L := sorry

end CategoryTheory.DerivedCategory
