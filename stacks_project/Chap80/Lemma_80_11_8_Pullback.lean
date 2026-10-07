module

public import stacks_project.Chap74.Definition_74_22_3_Pseudofunctor
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Lemma_78_5_2

/-!
# Slice pullback of actions of group algebraic spaces

Pulling a `G`-action back along `f : B' ⟶ B` yields a
`grpOverPullback G f`-action, together with the comparison of iterated
group pullbacks and transport of actions along group isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The action morphism of a slice-pulled module object. -/
def pullbackActionSmul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (grpOverPullback G f).X ⊗ (overPullback f).obj X.X ⟶ (overPullback f).obj X.X :=
  Functor.LaxMonoidal.μ (overPullback f) G.X X.X ≫ (overPullback f).map X.mod.smul

/-- The identity-action law for a slice-pulled module object. -/
theorem pullbackAction_one_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    η[(grpOverPullback G f).X] ⊵ₗ (overPullback f).obj X.X ≫ pullbackActionSmul f G X =
      (λₗ ((overPullback f).obj X.X)).hom := sorry

/-- The multiplication-action law for a slice-pulled module object. -/
theorem pullbackAction_mul_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    μ[(grpOverPullback G f).X] ⊵ₗ (overPullback f).obj X.X ≫ pullbackActionSmul f G X =
      (αₗ (grpOverPullback G f).X (grpOverPullback G f).X
          ((overPullback f).obj X.X)).hom ≫
        (grpOverPullback G f).X ⊴ₗ pullbackActionSmul f G X ≫
          pullbackActionSmul f G X := sorry

/-- Slice pullback of a `G`-action along `f : B' ⟶ B`. -/
def pullbackAction {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) : Action (grpOverPullback G f) where
  X := (overPullback f).obj X.X
  mod :=
    { smul := pullbackActionSmul f G X
      one_smul := pullbackAction_one_smul f G X
      mul_smul := pullbackAction_mul_smul f G X }

/-- The underlying object of a pulled-back action is the slice pullback of the
original object. -/
theorem pullbackAction_X {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (pullbackAction f G X).X = (overPullback f).obj X.X := sorry

/-- The action morphism of `pullbackAction f G X` is `pullbackActionSmul`. -/
theorem pullbackAction_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (pullbackAction f G X).mod.smul = pullbackActionSmul f G X := sorry

/-- Comparison of group objects `G_{B''}` obtained by pulling back along a
composite versus pulling back in stages. -/
def grpOverPullbackCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (G : GroupAlgebraicSpace B) :
    grpOverPullback G (g ≫ f) ≅ grpOverPullback (grpOverPullback G f) g :=
  Grp.mkIso ((overPullbackCompIso f g).app G.X) sorry sorry

/-- The underlying slice map of `grpOverPullbackCompIso` is the component of
`overPullbackCompIso`. -/
theorem grpOverPullbackCompIso_hom {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (G : GroupAlgebraicSpace B) :
    (grpOverPullbackCompIso f g G).hom.hom.hom =
      ((overPullbackCompIso f g).app G.X).hom := sorry

/-- Transport of a `G`-action along an isomorphism of group algebraic spaces
over the same base, by restriction of scalars along the inverse. -/
def actionCongr {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G G' : GroupAlgebraicSpace B} (e : G ≅ G') (X : Action G) : Action G' :=
  (CategoryTheory.Mod.comap e.inv.hom.hom).obj X

/-- Transport of actions along a group isomorphism preserves the underlying
object over the base. -/
theorem actionCongr_X {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G G' : GroupAlgebraicSpace B} (e : G ≅ G') (X : Action G) :
    (actionCongr e X).X = X.X := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
