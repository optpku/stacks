module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap81.Lemma_81_4_2_Pseudofunctor

/-!
# Glueing Type-valued small étale sheaves of algebraic spaces

The canonical functor from sheaves on `Y` to the `2`-fibre product of sheaves
on `Y'` and `Z` over sheaves on `E`, for a cartesian square of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Glue of Type-valued small étale sheaves along a cartesian square into the
`2`-fibre product of the pullback functors along the remaining two sides. -/
noncomputable def glueFunctor {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
      CategoricalPullback (pullback j) (pullback g) :=
  CatCommSqOver.comparison
    { fst := pullback f
      snd := pullback i
      iso :=
        pullbackComp f j ≪≫
          eqToIso (congrArg (fun h ↦ pullback h) h_cart.w) ≪≫
          (pullbackComp i g).symm }

/-- First projection of `glueFunctor` recovers pullback along `f`. -/
noncomputable def glueFunctor_fst {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ π₁ (pullback j) (pullback g) ≅ pullback f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Second projection of `glueFunctor` recovers pullback along `i`. -/
noncomputable def glueFunctor_snd {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ π₂ (pullback j) (pullback g) ≅ pullback i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The stored comparison iso of `glueFunctor` is `pullbackComp` transported
across the cartesian square. -/
theorem glueFunctor_iso {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((glueFunctor f i j g h_cart).obj F).iso =
      (pullbackComp f j).app F ≪≫
        (eqToIso (congrArg (fun h ↦ pullback h) h_cart.w)).app F ≪≫
        ((pullbackComp i g).symm).app F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
