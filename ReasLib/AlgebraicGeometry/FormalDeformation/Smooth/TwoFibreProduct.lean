/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.Postcompose
public import ReasLib.CategoryTheory.Cofibered.InGroupoids
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth

/-!
# Smoothness of comparison maps of two-fibre products

Tangent injectivity and infinitesimal-automorphism surjectivity imply smoothness of
postcomposition comparison maps between two-fibre products of cofibered groupoids.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open CofiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {H1 H2 G F :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.BasedFunctor

/-- If a morphism between deformation categories is injective on tangent spaces and
surjective on infinitesimal automorphisms, then the canonical comparison from a
two-fibre product over its domain to the two-fibre product over its codomain is smooth. -/
theorem isSmooth_mapPostcompose (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p]
    (hT : Function.Injective (differential (toBasedFunctor q)))
    (hInf : Function.Surjective (mapInfinitesimalAutomorphisms (toBasedFunctor q))) :
    IsSmooth (toBasedFunctor (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u}
      p1 p2 q)) := sorry

/-- The two-fibre-product comparison is smooth when its common-base morphism between
deformation categories is injective on tangent spaces and surjective on infinitesimal
automorphisms. -/
instance instIsSmoothMapPostcompose (p1 : H1 ⟶ G) (p2 : H2 ⟶ G) (q : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p]
    [hT : Fact (Function.Injective (differential (toBasedFunctor q)))]
    [hInf : Fact (Function.Surjective (mapInfinitesimalAutomorphisms (toBasedFunctor q)))] :
    IsSmooth (toBasedFunctor (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u}
      p1 p2 q)) :=
  isSmooth_mapPostcompose p1 p2 q hT.out hInf.out

end CategoryTheory.BasedFunctor
