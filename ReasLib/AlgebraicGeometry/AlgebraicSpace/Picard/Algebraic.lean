/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# Algebraicity of the Picard stack

The Picard stack of a flat, finitely presented, proper morphism of algebraic
spaces is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The natural 1-morphism from the Picard groupoid fibration to the coherent-sheaf
groupoid fibration sends each invertible module to its underlying coherent sheaf. -/
def toCohHom (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    toGroupoids f ⟶ CohStack.toGroupoids f :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toCoh f) (toCoh_p f))

/-- The underlying functor of the Picard-to-coherent-sheaf 1-morphism is `toCoh f`. -/
theorem toCohHom_toFunctor (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    FiberedCategoryOver.Groupoids.toFunctor (toCohHom f) = toCoh f := sorry

/-- The Picard-to-coherent-sheaf 1-morphism commutes strictly with the projections
to schemes over the base. -/
theorem toCohHom_p (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    FiberedCategoryOver.Groupoids.toFunctor (toCohHom f) ⋙ CohStack.p f = p f := sorry

/-- The Picard stack of a flat, finitely presented, proper morphism of algebraic
spaces over a scheme is an algebraic stack in Hom-universe `u + 1`. -/
instance instAlgebraicStack (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    CohStack.AlgebraicStack (toGroupoids f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
