/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WeilRestriction.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.23.4 (1): for a finitely presented, flat, pure morphism `X ⟶ S`, the
Weil restriction of a closed subscheme `Y ⟶ X` is represented by a closed immersion
into `S`. -/
@[stacks 07AI] #check
  (AlgebraicGeometry.Scheme.WeilRestriction.exists_closedImmersion_representation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation X.hom]
      [AlgebraicGeometry.Flat X.hom] [AlgebraicGeometry.IsClosedImmersion i.left]
      (h_pure : AlgebraicGeometry.Scheme.IsPureOver X.hom),
      ∃ Z : Over S,
        Nonempty
          ((AlgebraicGeometry.Scheme.WeilRestriction.ofClosedImmersion X Y i).RepresentableBy Z) ∧
          AlgebraicGeometry.IsClosedImmersion Z.hom)

/- Lemma 38.23.4 (2): if `Y ⟶ S` is also finitely presented, the closed immersion
representing its Weil restriction can be chosen finitely presented. -/
@[stacks 07AI] #check
  (AlgebraicGeometry.Scheme.WeilRestriction.exists_closedImmersion_representation_of_finitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation X.hom]
      [AlgebraicGeometry.Flat X.hom] [AlgebraicGeometry.IsClosedImmersion i.left]
      (h_pure : AlgebraicGeometry.Scheme.IsPureOver X.hom)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation Y.hom],
      ∃ Z : Over S,
        Nonempty
          ((AlgebraicGeometry.Scheme.WeilRestriction.ofClosedImmersion X Y i).RepresentableBy Z) ∧
          AlgebraicGeometry.IsClosedImmersion Z.hom ∧
            AlgebraicGeometry.Scheme.Hom.FinitePresentation Z.hom)
