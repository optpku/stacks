/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Concentration

/-!
# Cotangent Homology of Surjective Algebra Maps

@stack 07BP

This leaf specializes the presentation-level conormal identification to the
canonical first cotangent homology of a surjective algebra map.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Algebra.H1Cotangent

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 10.134.6 (2), tag `07BP`: the canonical first cotangent homology of a surjective
algebra map is linearly equivalent to the cotangent module of its canonical surjective
presentation. -/
@[stacks 07BP "surjective cotangent homology"]
noncomputable def equivOfSurjective
    (h : Function.Surjective (algebraMap A B)) :
    H1Cotangent A B ≃ₗ[B] (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent :=
  (Extension.ofSurjective (Algebra.ofId A B) h).h1CotangentEquivCotangent

end Algebra.H1Cotangent

namespace Algebra.NaiveCotangent.Surjective

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 10.134.6 (1), tag `07BP`: for a surjective algebra map, the canonical
naive cotangent complex is homotopy equivalent to the degree-one complex on
the conormal module of the canonical surjective presentation. -/
@[stacks 07BP "surjective naive cotangent concentration"]
theorem homotopyEquivSingleOne
    (h : Function.Surjective (algebraMap A B)) :
    Nonempty <|
      HomotopyEquiv (Algebra.naiveCotangent A B)
        ((HomologicalComplex.single (ModuleCat B) (ComplexShape.down ℕ) 1).obj
          (ModuleCat.of B
            (Algebra.Extension.NaiveCotangent.Lift
              (Extension.ofSurjective (Algebra.ofId A B) h)))) := sorry

end Algebra.NaiveCotangent.Surjective
