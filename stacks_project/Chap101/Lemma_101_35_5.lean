/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Characterization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.35.5: Étale morphisms of algebraic stacks are characterized by
universal algebraic-space tests and by an fppf covering square. -/
@[stacks 0CIQ] #check (AlgebraicGeometry.AlgebraicStack.Etale.tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    List.TFAE
      [Etale f,
        DM f ∧
          ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
            (U : AlgebraicSpace S)
            (p : U.toGroupoids ⟶
              TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
            Groupoids.Hom.Etale p →
              AlgebraicSpace.Etale (Etale.spaceMap f g p),
        ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
          (p : T.toGroupoids ⟶
            TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
          Groupoids.Hom.Surjective g ∧
            Groupoids.Hom.LocallyOfFinitePresentation g ∧
              Groupoids.Hom.Flat g ∧ Groupoids.Hom.Etale p ∧
                Groupoids.Hom.Surjective p ∧
                  AlgebraicSpace.Etale (Etale.spaceMap f g p)])
