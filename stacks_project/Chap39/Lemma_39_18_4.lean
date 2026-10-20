module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Stabilizer
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.18.4: the stabilizer of a restricted groupoid scheme is canonically the
pullback of the original stabilizer along the restricting morphism. -/
@[stacks 04ML]
#check (AlgebraicGeometry.GroupoidScheme.stabilizerPullbackIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U),
      (G.pullback g).stabilizer ≅ (Over.pullback g).mapGrp.obj G.stabilizer)
