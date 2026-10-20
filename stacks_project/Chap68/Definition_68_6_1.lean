module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conditions
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 68.6.1 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is decent if for every point `x ∈ |X|` the equivalent conditions of
Lemma 68.4.5 hold, in other words property (γ) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check (AlgebraicGeometry.AlgebraicSpace.IsDecent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 68.6.1 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is reasonable if the equivalent conditions of Lemma 68.4.6 hold, in
other words property (δ) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check (AlgebraicGeometry.AlgebraicSpace.IsReasonable :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 68.6.1 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is very reasonable if the equivalent conditions of Lemma 68.4.7 hold,
i.e., property (ε) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check (AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isDecent_iff_forallAffineEtaleFiniteAbove :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsDecent X ↔
      ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.forallAffineEtaleFiniteAbove X x)
