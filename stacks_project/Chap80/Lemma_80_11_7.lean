module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient

/-! Free actions of flat, locally finitely presented group algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 80.11.7: the fppf quotient of a free action is an algebraic space. -/
@[stacks 06PH] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action.hasAlgebraicSpaceQuotient_of_isFree :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom],
    (GroupoidAlgebraicSpace.ofAction G X).HasAlgebraicSpaceQuotient)

/- Lemma 80.11.7: the representing quotient morphism is surjective, flat,
and locally of finite presentation. -/
@[stacks 06PH] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action.quotientHom_surjective_flat_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)],
    AlgebraicSpace.Surjective q ∧ AlgebraicSpace.Flat q ∧
      AlgebraicSpace.LocallyOfFinitePresentation q)

/- Lemma 80.11.7: the restricted action over the quotient is an fppf torsor. -/
@[stacks 06PH] #check (AlgebraicGeometry.GroupAlgebraicSpace.Action.isStandardTorsor_over_quotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
    [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
    [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)]
    (f : F ⟶ B) (hq : q ≫ f = X.X.hom),
    GroupAlgebraicSpace.IsStandardTorsor (GroupAlgebraicSpace.baseChange G f)
      (AlgebraicGeometry.GroupAlgebraicSpace.Action.restrictTo G X f q hq h_eq)
      StandardTopology.fppf)

