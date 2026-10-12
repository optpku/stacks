/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Families underlying scheme covers

This module gives the direct fixed-target family presentation of a canonical
`Scheme.Cover`, so downstream constructions need not repeatedly unpack its
index type, source schemes, and arrows.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry.Scheme.Cover

/-- The fixed-target semi-representable family underlying a scheme-site cover. -/
abbrev toOverFamily {T : Scheme.{u}} {K : Precoverage Scheme.{u}}
    (cover : T.Cover K) : SemiRepresentableFamily.Over T :=
  ofArrows cover.X cover.f

/-- The `i`-th object of a cover's fixed-target family is the `i`-th cover
map. -/
@[simp] theorem toOverFamily_obj {T : Scheme.{u}} {K : Precoverage Scheme.{u}}
    (cover : T.Cover K) (i : cover.I₀) :
    cover.toOverFamily.obj i = Over.mk (cover.f i) := rfl

end AlgebraicGeometry.Scheme.Cover
