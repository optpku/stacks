/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.BaseChange

/-!
# Spec-fibre products of algebraic spaces

The sliced spectrum constructions and their pullback specifications are provided
by the mathematical owner imported here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.specMap_w :
  ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'),
    Spec.map φ ≫ specULiftZIsTerminal.from (Spec R) =
      specULiftZIsTerminal.from (Spec R'))

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeSpec :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}},
    (globalSectionsRing X ⟶ A') → AlgebraicSpace S)
