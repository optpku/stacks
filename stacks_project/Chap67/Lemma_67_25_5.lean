/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
import StacksCheckRecall

/-!
# Images of finite type points under surjective locally finite type morphisms

A surjective locally-of-finite-type morphism of algebraic spaces sends finite-type
points onto finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/- Lemma 67.25.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type and surjective, then
`Points.map f '' finiteTypePoints X = finiteTypePoints Y`. -/
@[stacks 06EJ] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.image_finiteTypePoints_eq_of_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [Surjective f],
      Points.map f '' finiteTypePoints X = finiteTypePoints Y)

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
