/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- The scheme-theoretic image of a partial section of a separated morphism of
algebraic stacks representable by algebraic spaces restricts to an equivalence
over the base after pullback to the quasi-compact open substack on which the
section is defined. -/
theorem isEquivalence_snd_of_section {S : Scheme.{u}}
    {X Y V Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack V] [AlgebraicStack Y']
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) [Separated f]
    (ιV : V ⟶ Y) [OpenImmersion ιV] [QuasiCompact ιV]
    (s : V ⟶ X) (hs : s ≫ f ≅ ιV) (toImage : V ⟶ Y') (ι : Y' ⟶ X)
    [IsSchemeTheoreticImage s toImage ι] :
    (CategoryTheory.FiberedCategoryOver.Groupoids.toBasedFunctor
      (CategoryTheory.TwoFibreProduct.snd.{u + 1, u, u + 1, u} (ι ≫ f) ιV)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
