/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.ExactSequence

/-!
# Two-fibre products of deformation categories

The two-fibre product is a deformation category, and its canonical six-term
sequence of infinitesimal automorphism spaces and tangent spaces is exact.
-/

@[expose] public section

open CategoryTheory Functor CofiberedCategoryOver.Groupoids
open CategoryTheory.BasedFunctor
open scoped Bicategory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
variable (f : H ⟶ F) (g : G ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p]

/- Lemma 90.20.1 (1): the two-fibre product of a cospan of deformation categories
is a deformation category. -/
@[stacks 06L5] #check
  (CategoryTheory.Functor.instIsDeformationCategory_twoFibreProduct f g :
    IsDeformationCategory (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)))

/- Lemma 90.20.1 (2): the canonical six-term sequence of infinitesimal automorphism
spaces and tangent spaces is exact; binary products represent the finite direct sums. -/
@[stacks 06L5] #check
  (CategoryTheory.BasedFunctor.infTangentSequence_exact f g :
    Function.Injective (infProdLinearMap f g) ∧
      Function.Exact (infProdLinearMap f g) (infDiffLinearMap f g) ∧
      Function.Exact (infDiffLinearMap f g) (connectingLinearMap f g) ∧
      Function.Exact (connectingLinearMap f g) (tangentProdLinearMap f g) ∧
      Function.Exact (tangentProdLinearMap f g) (tangentDiffLinearMap f g))
