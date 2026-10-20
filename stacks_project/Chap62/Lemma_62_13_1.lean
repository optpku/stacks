/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition

/-!
# Bilinearity of composition of families of cycles on fibres

Composition of families of cycles on fibres is additive in each family.
-/

open AlgebraicGeometry CategoryTheory

universe u

variable {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
  [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}

/- Lemma 62.13.1 (1): composition is additive in the first family. -/
@[stacks 0H6I] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_add_left p f
    (r := (r : ℤ)) (e := (e : ℤ)) :
    ∀ (α₁ α₂ : Scheme.Hom.CyclesOnFibers f (r : ℤ))
      (β : Scheme.Hom.CyclesOnFibers p (e : ℤ)),
      Scheme.Hom.CyclesOnFibers.comp (α₁ + α₂) β =
        Scheme.Hom.CyclesOnFibers.comp α₁ β + Scheme.Hom.CyclesOnFibers.comp α₂ β)

/- Lemma 62.13.1 (2): composition is additive in the second family. -/
@[stacks 0H6I] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_add_right p f
    (r := (r : ℤ)) (e := (e : ℤ)) :
    ∀ (α : Scheme.Hom.CyclesOnFibers f (r : ℤ))
      (β₁ β₂ : Scheme.Hom.CyclesOnFibers p (e : ℤ)),
      Scheme.Hom.CyclesOnFibers.comp α (β₁ + β₂) =
        Scheme.Hom.CyclesOnFibers.comp α β₁ + Scheme.Hom.CyclesOnFibers.comp α β₂)
