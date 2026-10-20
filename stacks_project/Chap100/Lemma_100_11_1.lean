/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldCover
import StacksCheckRecall

/-!
# Field-spectrum morphisms into an algebraic stack with a flat surjective field cover

If an algebraic stack over a scheme admits one surjective flat morphism from the
spectrum of a field, then every morphism from the spectrum of a field is
surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.11.1: If an algebraic stack admits a surjective flat field-spectrum
cover, every field-spectrum morphism into it is surjective and flat. -/
@[stacks 06MM] #check
  (AlgebraicGeometry.AlgebraicStack.surjective_and_flat_of_specField_cover :
    ∀ {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
      {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
      (cover : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
      [Groupoids.Hom.Surjective cover] [Groupoids.Hom.Flat cover]
      {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
      (f : GroupoidsOver.slice (Over.mk σ') ⟶ Z),
      Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f)
