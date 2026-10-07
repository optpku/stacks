module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Compatibility
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology

@[expose] public section

/-!
# Legacy Cohomology API for Sequential Derived Limits

The canonical short exact sequence is owned by `HomotopyLimit.IsOf.cohomologyShortExact`.
This leaf retains the total-derived-functor cohomology object, which is genuinely specific to
derived categories, and the historical `IsDerivedLimit` form of the short exact sequence.
@stack 07KY
@stack 08U5
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

namespace DerivedLimit

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory C]
variable [HasDerivedCategory (SequentialInverseSystem C)]
variable [IsGrothendieckAbelian.{w} (SequentialInverseSystem C)]
variable [HasLimitsOfShape ℕᵒᵖ C]

/-- The degree-`p` cohomology object of the canonical total right derived inverse limit of `K`. -/
@[stacks 07KY, stacks 08U5 "cohomology of the canonical derived inverse limit"]
abbrev cohomology
    (K : DerivedCategory (SequentialInverseSystem C)) (p : ℤ) : C :=
  (DerivedCategory.homologyFunctor C p).obj ((functor C).obj K)

end

end DerivedLimit

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

namespace IsDerivedLimit

/-- Lemma 15.87.10 (Stacks 07KY): compatibility form of the cohomology Milnor short exact
sequence for a legacy `IsDerivedLimit` witness. -/
@[stacks 07KY, stacks 08U5]
theorem cohomologyShortExact
    {Ksys : SequentialInverseSystem (DerivedCategory C)} {Klim : DerivedCategory C}
    (hKlim : IsDerivedLimit Ksys Klim) (p : ℤ) :
    ∃ (ι : DerivedLimit.R1
        (Ksys ⋙ DerivedCategory.homologyFunctor C (p - 1)) ⟶
        (DerivedCategory.homologyFunctor C p).obj Klim)
      (π : (DerivedCategory.homologyFunctor C p).obj Klim ⟶
        limit (Ksys ⋙ DerivedCategory.homologyFunctor C p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end IsDerivedLimit

end CategoryTheory
