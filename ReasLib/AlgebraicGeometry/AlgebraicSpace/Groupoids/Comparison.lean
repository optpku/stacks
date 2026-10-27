/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids

/-!
# Identity and composition comparisons for algebraic-space groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.toGroupoids

variable {S : Scheme.{u}}

/-- The identity comparison for `AlgebraicSpace.toGroupoids.map`, obtained from
the `map_id` fields of `Sets.ofPresheaf` and `Sets.toGroupoids`. -/
def mapIdIso {U : AlgebraicSpace S} :
    AlgebraicSpace.toGroupoids.map (𝟙 U) ≅ 𝟙 U.toGroupoids :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map_id U.functorOfPoints)).trans
      ((Sets.toGroupoids (Over S)).map_id
        ((Sets.ofPresheaf (Over S)).obj U.functorOfPoints))

/-- The composition comparison for `AlgebraicSpace.toGroupoids.map`, obtained
from the `map_comp` fields of `Sets.ofPresheaf` and `Sets.toGroupoids`. -/
def mapCompIso {U V W : AlgebraicSpace S} (f : U ⟶ V) (g : V ⟶ W) :
    AlgebraicSpace.toGroupoids.map (f ≫ g) ≅
      AlgebraicSpace.toGroupoids.map f ≫ AlgebraicSpace.toGroupoids.map g :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map_comp f g)).trans
      ((Sets.toGroupoids (Over S)).map_comp
        ((Sets.ofPresheaf (Over S)).map f) ((Sets.ofPresheaf (Over S)).map g))

end AlgebraicGeometry.AlgebraicSpace.toGroupoids
