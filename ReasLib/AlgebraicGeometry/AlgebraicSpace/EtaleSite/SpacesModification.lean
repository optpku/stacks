/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Étale algebraic spaces on proper modifications

Canonical base change compares étale spaces over an algebraic space with compatible
pairs over a proper modification and a closed subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical isomorphism of successive spaces-étale pullbacks along a
cartesian square, identifying `spacesEtalePullback f ⋙ spacesEtalePullback j`
with `spacesEtalePullback i ⋙ spacesEtalePullback g`. -/
noncomputable def spacesEtaleGlueIso {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    spacesEtalePullback f ⋙ spacesEtalePullback j ≅
      spacesEtalePullback i ⋙ spacesEtalePullback g :=
  (spacesEtalePullbackComp j f).symm ≪≫
    eqToIso (congrArg (fun h ↦ spacesEtalePullback h) h_cart.w) ≪≫
    spacesEtalePullbackComp g i

/-- Glue of étale algebraic spaces along a cartesian square into the `2`-fibre
product of the pullback functors along the remaining two sides. -/
noncomputable def spacesEtaleGlueFunctor {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    spacesEtaleSite Y ⥤
      CategoricalPullback (spacesEtalePullback j) (spacesEtalePullback g) :=
  CatCommSqOver.comparison
    { fst := spacesEtalePullback f
      snd := spacesEtalePullback i
      iso := spacesEtaleGlueIso f i j g h_cart }

/-- First projection of `spacesEtaleGlueFunctor` recovers pullback along `f`. -/
noncomputable def spacesEtaleGlueFunctor_fst {S : Scheme.{u}}
    {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    spacesEtaleGlueFunctor f i j g h_cart ⋙
      π₁ (spacesEtalePullback j) (spacesEtalePullback g) ≅
      spacesEtalePullback f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Second projection of `spacesEtaleGlueFunctor` recovers pullback along `i`. -/
noncomputable def spacesEtaleGlueFunctor_snd {S : Scheme.{u}}
    {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    spacesEtaleGlueFunctor f i j g h_cart ⋙
      π₂ (spacesEtalePullback j) (spacesEtalePullback g) ≅
      spacesEtalePullback i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The stored comparison iso of `spacesEtaleGlueFunctor` is the component of
`spacesEtaleGlueIso`. -/
theorem spacesEtaleGlueFunctor_iso {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) (V : spacesEtaleSite Y) :
    ((spacesEtaleGlueFunctor f i j g h_cart).obj V).iso =
      (spacesEtaleGlueIso f i j g h_cart).app V :=
  sorry

/-- A proper morphism that is an isomorphism outside a closed subspace induces an
equivalence between étale spaces over the base and compatible pairs of étale spaces
over its source and the closed subspace. -/
@[stacks 0GG1]
theorem spacesEtaleGlueFunctor_isEquivalence {S : Scheme.{u}}
    {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (spacesEtaleGlueFunctor f i j g h_cart).IsEquivalence :=
  sorry

/-- If `E` is the chosen fibre product `Z ×_Y Y'`, then `spacesEtaleGlueFunctor`
is an equivalence. -/
theorem spacesEtaleGlueFunctor_isEquivalence_of_hasPullback
    {S : Scheme.{u}} {Y' Y Z : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (spacesEtaleGlueFunctor f i (Limits.pullback.snd i f) (Limits.pullback.fst i f)
      (IsPullback.of_hasPullback i f).flip).IsEquivalence :=
  spacesEtaleGlueFunctor_isEquivalence f i (Limits.pullback.snd i f)
    (Limits.pullback.fst i f) (IsPullback.of_hasPullback i f).flip h_iso

/-- The comparison functor for a proper modification is canonically an equivalence
when the modification is an isomorphism over the complement of the closed subspace. -/
instance spacesEtaleGlueFunctorIsEquivalence {S : Scheme.{u}}
    {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
    [IsIso (openInverseImageTo f (closedImmersionComplementι i))] :
    (spacesEtaleGlueFunctor f i j g h_cart).IsEquivalence :=
  spacesEtaleGlueFunctor_isEquivalence f i j g h_cart
    (inferInstance : IsIso (openInverseImageTo f (closedImmersionComplementι i)))

end AlgebraicGeometry.AlgebraicSpace
