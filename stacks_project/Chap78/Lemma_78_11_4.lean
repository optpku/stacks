module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 78.11.4 (1): The square formed by the two projections from the algebraic space of
composable arrows and the source and target maps is a fibre product; Stacks `pr₀` is
`pullback.fst G.s G.t` and `pr₁` is `pullback.snd G.s G.t`. -/
@[stacks 043Z] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fstSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t)

/- Lemma 78.11.4 (2): The square formed by composition, the second projection, and two copies
of the source map is a fibre product. -/
@[stacks 043Z] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.compSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback G.c (pullback.snd G.s G.t) G.s G.s)

/- Lemma 78.11.4 (3): The square formed by the first projection, composition, and two copies
of the target map is cartesian. -/
@[stacks 043Z] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fstCompIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback (pullback.fst G.s G.t) G.c G.t G.t)
