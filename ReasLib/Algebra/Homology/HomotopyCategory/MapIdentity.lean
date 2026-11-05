/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # The identity functor on homotopy categories

The canonical cochain identity is lifted using Mathlib's quotient construction.
Object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.Functor

/-- The functor on homotopy categories induced by the identity functor is canonically
isomorphic to the identity functor. -/
noncomputable def mapHomotopyCategoryIdIso (A : Type u) [Category.{v} A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

end CategoryTheory.Functor

