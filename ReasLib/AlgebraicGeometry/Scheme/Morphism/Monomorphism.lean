/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A monomorphism of schemes is injective on its underlying points. -/
theorem injectiveOfMono {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective f := sorry

end AlgebraicGeometry.Scheme.Hom
