module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Affine infinitesimal lifting for smooth algebraic stacks

Morphisms into a smooth algebraic stack extend across first-order thickenings
of affine schemes, compatibly with the specified structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- A morphism into a smooth algebraic stack extends across a first-order
thickening of affine schemes as a dotted arrow compatible with the specified
outer comparison isomorphism. -/
@[stacks 0DNZ]
theorem exists_lift {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f) :
    Nonempty (DottedArrow (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
      Bicategory.PseudoPullbackCone (𝟙 (GroupoidsOver.slice T')) f)) := sorry

/-- A morphism into a smooth algebraic stack extends across an affine first-order
thickening with restriction and structure-map comparison isomorphisms whose
pasted composite equals the specified outer comparison. -/
theorem exists_hom {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f) :
    ∃ (x' : GroupoidsOver.slice T' ⟶ X') (α : slice.pullback i x' ≅ x)
      (β : 𝟙 (GroupoidsOver.slice T') ≅ x' ≫ f),
      whiskerLeftIso (overMap i) β ≪≫ (α_ (overMap i) x' f).symm ≪≫
        whiskerRightIso α f = γ := sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
