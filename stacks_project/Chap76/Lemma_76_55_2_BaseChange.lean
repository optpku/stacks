module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
public import stacks_project.Chap67.Remark_67_22_4
public import stacks_project.Chap76.Lemma_76_55_2_EtaleLocal

/-!
# Base change of at-worst-nodal morphisms of algebraic spaces

The étale-local-on-source-and-target lift of at-worst-nodal of relative
dimension 1 is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
  MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AtWorstNodal

/-- The étale-local lift of at-worst-nodal of relative dimension 1 is stable
under arbitrary base change of morphisms of algebraic spaces. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    (etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) :
      MorphismProperty (AlgebraicSpace S)).IsStableUnderBaseChange :=
  sorry

/-- At-worst-nodal of relative dimension 1, as a property of morphisms of
algebraic spaces, is stable under pullback along an arbitrary morphism,
expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    (hg : etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) g) :
    etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a morphism of algebraic
spaces that is at worst nodal of relative dimension 1 is at worst nodal of
relative dimension 1. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f)
    (g : Z ⟶ Y) [HasPullback f g] :
    etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u})
      (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AtWorstNodal
