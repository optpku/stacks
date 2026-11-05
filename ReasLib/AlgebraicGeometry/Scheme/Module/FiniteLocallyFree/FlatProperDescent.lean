/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Flat proper descent of finite locally free modules

Finite locally free modules descend along suitable flat proper morphisms to normal
Noetherian schemes when their restrictions over stalks of codimension at most one are free.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FlatDescent

/-- A finite locally free module on the source of a flat proper morphism to a normal
Noetherian scheme descends to the base if it is free after base change to every stalk
spectrum of dimension at most one and the canonical structure-sheaf pushforward map is an
isomorphism.

The dimension-zero case includes the generic points of every irreducible component, including
zero-dimensional components. It is necessary: over a field, the height-one condition alone is
vacuous and does not exclude `𝒪(1)` on the projective line. Stacks Tag 0EXG omits this case in
its statement. Its canonical evaluation argument must check both dimensions zero and one
before the depth argument handles codimension at least two. The all-reduced-fibres hypothesis
of Tag 0EXH supplies the generic triviality needed in that application. -/
theorem existsFiniteLocallyFreePullback
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [IsNoetherian S]
    (hSnormal : S.isNormal)
    [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (hfree : ∀ s : S, ringKrullDim (S.presheaf.stalk s) ≤ 1 →
      ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E).IsFree) :
    ∃ (F : S.Modules) (_ : F.IsFiniteLocallyFree),
      Nonempty (E ≅ (Scheme.Modules.pullback f).obj F) := sorry

end AlgebraicGeometry.Scheme.Hom.FlatDescent
