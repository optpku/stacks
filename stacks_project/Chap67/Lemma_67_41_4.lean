/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Separated
import StacksCheckRecall

/-!
# Pushing down a valuative lift along a separated morphism

If a valuative square for a separated morphism of algebraic spaces is filled
after an arbitrary field extension of the fraction field, then the original
dotted arrow exists.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCommSq.Extension

/- Lemma 67.41.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a separated morphism
of algebraic spaces over `S`. Suppose given a diagram as in Definition 67.41.1
with `K ⊂ K'` arbitrary. Then the dotted arrow exists making the diagram
commute. -/
@[stacks 0ARH] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq.Extension.hasLift :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Separated f]
    {sq : ValuativeCommSq f} (e : sq.Extension), sq.commSq.HasLift)

/- A separated morphism of algebraic spaces admits a dotted lift
`Spec(R) ⟶ X` of a valuative square whenever an arbitrary extension of that
square already has a lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq.Extension.exists_liftHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Separated f]
    {sq : ValuativeCommSq f} (e : sq.Extension),
    ∃ l : ofOver sq.specR ⟶ X, sq.verticalMap ≫ l = sq.i₁ ∧ l ≫ f = sq.i₂)

end ValuativeCommSq.Extension
end AlgebraicGeometry.AlgebraicSpace
