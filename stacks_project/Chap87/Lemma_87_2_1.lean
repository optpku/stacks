/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.FormalScheme.Affine
import StacksCheckRecall

/-!
# Lemma 87.2.1

The restricted functor of points detects all morphisms from formal schemes of bounded size.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/- Lemma 87.2.1. Choose a category of schemes `Sch_α` as in Sets, Lemma 3.9.2.
Given a formal scheme `X`, its functor of points on `(Sch_α)ᵒᵖ` is
`(functorOfPoints P).obj X`, with value
`toFormalScheme.obj (P.ι.obj S) ⟶ X` at a scheme `S` in `Sch_α`. Then
morphisms `X ⟶ Y` of formal schemes are in bijection with morphisms
`(functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y` provided the size of
`X` is not too large, meaning `X.size` is at most the size of some scheme
satisfying `P`. -/
@[stacks 0AI1] #check (AlgebraicGeometry.FormalScheme.functorOfPoints_map_bijective :
    ∀ {P : ObjectProperty Scheme.{u}} (hP : Scheme.IsSmallBoundClosed P)
      {X Y : FormalScheme.{u}} (hX : ∃ S, P S ∧ X.size ≤ S.size),
      Function.Bijective
        ((functorOfPoints P).map :
          (X ⟶ Y) → ((functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y)))

end AlgebraicGeometry.FormalScheme
