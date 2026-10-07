module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.Extend
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import stacks_project.Chap88.«88_3_0_1»

/-!
# Derived completed naive cotangent objects

This leaf sends a finite completed presentation's two-term Jacobian complex
`NL_{B/A}^∧` to its object in `D(B)`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/-- The object of `D(B)` represented by the completed naive cotangent complex
`NL_{B/A}^∧` of a finite completed presentation. -/
noncomputable abbrev naiveCotangentObject (I : Ideal A) (P : Presentation A B I ι) :
    DerivedCategory (ModuleCat B) :=
  DerivedCategory.Q.obj ((naiveCotangent I P).extend ComplexShape.embeddingDownNat)

/-- Unfolding of the derived completed naive cotangent object. -/
theorem naiveCotangentObject_eq (I : Ideal A) (P : Presentation A B I ι) :
    naiveCotangentObject I P =
      DerivedCategory.Q.obj ((naiveCotangent I P).extend ComplexShape.embeddingDownNat) :=
  sorry

/-- The completed naive cotangent object is concentrated in degrees `≥ -1`. -/
theorem naiveCotangentObject_isGE (I : Ideal A) (P : Presentation A B I ι) :
    (naiveCotangentObject I P).IsGE (-1) :=
  sorry

/-- The completed naive cotangent object is concentrated in degrees `≤ 0`. -/
theorem naiveCotangentObject_isLE (I : Ideal A) (P : Presentation A B I ι) :
    (naiveCotangentObject I P).IsLE 0 :=
  sorry

end Algebra.NaiveCotangent.Adic
