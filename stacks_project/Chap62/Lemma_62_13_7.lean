/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.Cap

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/- Lemma 62.13.7. Let `(S, δ)` be as in Situation 42.7.1, and let
`X ⟶ Y ⟶ Z` be morphisms of schemes locally of finite type over `S`.
Composition of families of `r`- and `s`-cycles on fibres, followed by the cap
action of an `e`-cycle on `Z`, equals the successive cap actions in degree
`r + s + e` on `X`, for nonnegative `r`, `s`, and `e`.
-/
@[stacks 0H6P] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_comp :
    ∀ {S X Y Z : Scheme.{u}} [UniversallyCatenary S]
      (p : Z ⟶ S) (g : Y ⟶ Z) (f : X ⟶ Y)
      [LocallyOfFiniteType p] [LocallyOfFiniteType g] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] {r s e : ℕ}
      (α : CyclesOnFibers f (r : ℤ)) (β : CyclesOnFibers g (s : ℤ))
      (γ : CycleGroup Z (p.relativeDimensionFunction δ) (e : ℤ)),
      CycleGroup.toAlgebraicCycle (((f ≫ g) ≫ p).relativeDimensionFunction δ)
          ((r : ℤ) + (s : ℤ) + (e : ℤ)) (cap p (f ≫ g) δ (comp α β) γ) =
        CycleGroup.toAlgebraicCycle ((f ≫ g ≫ p).relativeDimensionFunction δ)
          ((r : ℤ) + ((s : ℤ) + (e : ℤ)))
          (cap (g ≫ p) f δ α (cap p g δ β γ)))

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
