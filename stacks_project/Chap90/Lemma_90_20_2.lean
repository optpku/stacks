/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.TwoFibreProduct
import StacksCheckRecall

open CategoryTheory ArtinianLocalAlgCat Functor
open CofiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

universe u

/- Lemma 90.20.2: tangent injectivity and infinitesimal-automorphism surjectivity for a
morphism of deformation categories imply smoothness of the canonical comparison of
two-fibre products. -/
@[stacks 0DYN] #check (CategoryTheory.BasedFunctor.isSmooth_mapPostcompose :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {H1 H2 G F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)}
    (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p],
    Function.Injective (BasedFunctor.differential (toBasedFunctor q)) →
    Function.Surjective (BasedFunctor.mapInfinitesimalAutomorphisms (toBasedFunctor q)) →
    BasedFunctor.IsSmooth (toBasedFunctor
      (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} p1 p2 q)))
