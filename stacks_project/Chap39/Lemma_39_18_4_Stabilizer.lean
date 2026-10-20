module

public import stacks_project.Chap39.Lemma_39_3_2_Pullback
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Stabilizer

@[expose] public section

open CategoryTheory

universe u

/- The stabilizer base-change construction remains available through this compatibility module. -/
#check (@AlgebraicGeometry.Scheme.PreRelation.stabilizerPullbackIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S}
    (P : AlgebraicGeometry.Scheme.PreRelation U) (g : U' ⟶ U),
      (P.pullback g).stabilizer ≅ (Over.pullback g).obj P.stabilizer)
