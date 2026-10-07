module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Base change of relatively perfect derived modules on algebraic spaces

Relative perfectness for a flat, locally finitely presented morphism of algebraic
spaces is preserved by derived pullback along an arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo

/-- Derived pullback along a base change preserves relative perfectness over a flat,
locally finitely presented morphism of algebraic spaces. -/
theorem baseChange {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (g : Y' ⟶ Y) (K : ModuleDerived X)
    (hK : IsPerfectRelativeTo f K) :
    IsPerfectRelativeTo (Limits.pullback.snd f g)
      ((ModuleDerived.pullback (Limits.pullback.fst f g)).obj K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
