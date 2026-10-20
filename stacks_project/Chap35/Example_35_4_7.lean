/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.UniversallyInjective

@[expose] public section

universe u v

/- Example 35.4.7: if a finite family generates the unit ideal, then the canonical map
`R → ∀ i : Fin n, Localization.Away (f i)` to the product of the corresponding
principal localizations is universally injective. -/
@[stacks 08WN] #check
  (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap_universallyInjective :
    ∀ {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R),
      Ideal.span (Set.range f) = ⊤ →
        LinearMap.UniversallyInjective.{u, u, u, v}
          (Algebra.linearMap R (∀ i : Fin n, Localization.Away (f i))))
