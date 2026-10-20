/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over

/-!
# Faithfulness of pullback for scheme descent data

Criteria ensuring that pullback along a commutative square is faithful on singleton-family
scheme descent data.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

/-- Pullback on singleton-family descent data is faithful when the top morphism of the
commutative square is flat and surjective. -/
instance instFaithfulFunctorOfFlatSurjective {X X' S S' : Scheme.{u}}
    (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S) (f : X' ⟶ X)
    (sq : CommSq f a' a h) [Flat f] [Surjective f] :
    (functor a a' h f sq).Faithful := sorry

/-- Pullback on singleton-family descent data along a morphism over a fixed base is faithful
when the source structure morphism is flat and surjective. -/
instance instFaithfulFunctorOfFlatSurjectiveDomain {X X' S : Scheme.{u}}
    (a : X ⟶ S) (a' : X' ⟶ S) (f : X ⟶ X') (sq : CommSq f a a' (𝟙 S))
    [Flat a] [Surjective a] :
    (functor a' a (𝟙 S) f sq).Faithful := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback
