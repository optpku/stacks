/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.Flat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Covering families supplied by representable flatness

This leaf separates the functor-theoretic nonemptiness of structured-arrow
categories from its site-theoretic singleton-cover consequence.
-/

@[expose] public section

universe uC uD vC vD

namespace CategoryTheory

open SemiRepresentableFamily.Over

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace RepresentablyFlat

/-- For any Grothendieck topology, a representably flat functor supplies a covering family whose
members each map to an object in the functor's image. -/
theorem existsCoveringFamily
    (u : C ⥤ D) [RepresentablyFlat u] (K : GrothendieckTopology D) (V : D) :
    ∃ 𝒱 : SemiRepresentableFamily.Over V,
      IsCovering K.toPrecoverage 𝒱 ∧
        ∀ i : 𝒱.index, Nonempty (StructuredArrow (𝒱.obj i).left u) := sorry

end RepresentablyFlat

end CategoryTheory
