/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Situation 81.10.6: standing formal-glueing setup over a base scheme `S`. A
quasi-compact and quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over `S`
and a finite-presentation closed immersion `i : Z ⟶ X` are given, with
`inverseImageTo f i` an isomorphism and `f` flat at every point of
`pointsImage (inverseImageι f i)`. The derived opens are
`closedImmersionComplement i` and `closedImmersionComplement (inverseImageι f i)`,
and `restrictToComplement f i` fills the commutative square. -/
@[stacks 0AEV] #check (AlgebraicGeometry.AlgebraicSpace.IsFormalGlueing :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [QuasiCompact f] → [QuasiSeparated f] → [IsClosedImmersion i] →
    [FinitePresentation i] → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.restrictToComplement :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] →
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i)

#check (AlgebraicGeometry.AlgebraicSpace.restrictToComplementCommSq :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [IsClosedImmersion i] →
    CommSq (restrictToComplement f i) (closedImmersionComplementι (inverseImageι f i))
      (closedImmersionComplementι i) f)
