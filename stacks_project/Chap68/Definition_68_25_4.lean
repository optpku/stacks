/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 68.25.4: Let `S` be a scheme. Let `X` be a decent and locally
Noetherian algebraic space over `S`. We say `X` is universally catenary if for
every morphism `Y ⟶ X` of algebraic spaces which is locally of finite type and
with `Y` decent, the algebraic space `Y` is catenary. -/
@[stacks 0ED7] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.universallyCatenary_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary X ↔
      AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X ∧
        AlgebraicGeometry.AlgebraicSpace.IsDecent X ∧
          ∀ {Y : AlgebraicGeometry.AlgebraicSpace S} (f : Y ⟶ X),
            AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f →
              AlgebraicGeometry.AlgebraicSpace.IsDecent Y →
                AlgebraicGeometry.AlgebraicSpace.IsCatenary Y)
