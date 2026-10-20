module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap86.«86_3_2_1_Pushforward»
public import stacks_project.Chap86.«86_7_0_1_Pullback»

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.map :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (sq : CommSq g' f' f g),
    pushforwardCohomologyIn f ⋙ pullback g ⟶ pullback g' ⋙ pushforwardCohomologyIn f')
