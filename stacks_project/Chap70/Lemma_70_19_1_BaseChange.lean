module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange

/-! # Base change of morphisms that are isomorphisms over an open -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.overPullback :
  ∀ {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W), Over W ⥤ Over V)

#check (AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.baseChange :
  ∀ {S : Scheme.{u}} {V W U : AlgebraicSpace S}
    (f : V ⟶ W) (ι : U ⟶ W) [IsOpenImmersion ι],
    IsoOverOpen ι ⥤ IsoOverOpen (openInverseImageι f ι))
