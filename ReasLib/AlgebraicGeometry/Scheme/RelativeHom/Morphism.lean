/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/-- Morphisms over `T.left` between the ordered base changes `T ×_S Z` and `T ×_S X`. -/
abbrev BaseChangeMorphism {S : Scheme.{u}} (Z X T : Over S) : Type u :=
  ((Over.mk (pullback.fst T.hom Z.hom) : Over T.left) ⟶
    (Over.mk (pullback.fst T.hom X.hom) : Over T.left))

end AlgebraicGeometry.Scheme.RelativeHom
