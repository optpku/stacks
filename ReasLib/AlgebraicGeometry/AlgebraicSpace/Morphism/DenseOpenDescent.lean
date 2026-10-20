module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Descent of morphisms of algebraic spaces along a dense open

For morphisms `f : X ⟶ Y` and `g : X ⟶ Z` over `B`, with `Y` separated over
`B` and `g` surjective, flat, and locally of finite presentation, a factorization
of `f` over a scheme-theoretically dense open of `Z` extends through `g`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `f : X ⟶ Y` and `g : X ⟶ Z` be morphisms of algebraic spaces over `B`.
If `Y` is separated over `B`, `g` is surjective, flat, and locally of finite
presentation, and `f` factors through a scheme-theoretically dense open of `Z`
on its inverse image, then `f` factors through `g` over `B`. -/
@[stacks 0AEL]
theorem exists_desc_of_isSchemeTheoreticallyDense
    {S : Scheme.{u}} {B X Y Z V : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [OverClass Z B] [Separated (Y ↘ B)]
    {f : X ⟶ Y} {g : X ⟶ Z} [HomIsOver f B] [HomIsOver g B]
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (ι : V ⟶ Z) [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι]
    (hV : V ⟶ Y)
    (hV_fac : openInverseImageι g ι ≫ f = openInverseImageTo g ι ≫ hV) :
    ∃ h : Z ⟶ Y, HomIsOver h B ∧ g ≫ h = f := sorry

end AlgebraicGeometry.AlgebraicSpace
