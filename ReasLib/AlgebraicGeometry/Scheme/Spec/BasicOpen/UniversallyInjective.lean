/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.FaithfullyFlat
public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat

@[expose] public section

universe u v

namespace AlgebraicGeometry.Spec.BasicOpenUnion

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The canonical map from a ring to the product of its principal localizations at a finite
family generating the unit ideal is universally injective. -/
theorem localizationProductMap_universallyInjective (f : Fin n → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    LinearMap.UniversallyInjective.{u, u, u, v}
      (Algebra.linearMap R (∀ i : Fin n, Localization.Away (f i))) := sorry

end AlgebraicGeometry.Spec.BasicOpenUnion
