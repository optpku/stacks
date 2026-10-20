module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.BaseChange

/-!
# Base change of relatively perfect derived modules on algebraic spaces

Relative perfectness for a flat, locally finitely presented morphism of algebraic
spaces is preserved by derived pullback along an arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo.baseChange :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y)
      (K : ModuleDerived X),
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f K →
        AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
          (pullback.snd f g)
          ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback (pullback.fst f g)).obj K))
