/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap66.Lemma_66_18_8_Pullback

/-!
# Glueing étale algebraic spaces along a cartesian square

The canonical functor from the étale site of algebraic spaces over `Y` to the
`2`-fibre product of the étale sites over `Y'` and `Z` over the étale site over
`E`, for a cartesian square of algebraic spaces.
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

end AlgebraicGeometry.AlgebraicSpace
