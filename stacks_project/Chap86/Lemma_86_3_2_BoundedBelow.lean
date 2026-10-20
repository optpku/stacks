module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.BoundedBelow

/-!
# Lower bound for the right adjoint of derived pushforward

A chosen right adjoint of restricted derived pushforward on `DerivedQCoh`
along a morphism of quasi-compact quasi-separated algebraic spaces preserves
lower cohomological bounds up to a uniform integer shift.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_mapsBoundedBelow :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
      (f : X ⟶ Y) →
      (a : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh Y ⥤
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X) →
      (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) →
      ∀ K : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh Y,
        K.obj.IsBoundedBelow → (a.obj K).obj.IsBoundedBelow)
