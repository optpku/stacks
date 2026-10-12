/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap81.Lemma_81_3_2_Pullback

/-!
# Lemma 81.3.2

A cocone of algebraic spaces over `B` is a colimit as soon as some fpqc covering
of the apex is a colimit after base change to members and pairwise overlaps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.3.2: Let `S` be a scheme and `B` an algebraic space over `S`. Let
`D : J ⥤ Over B` be a diagram of algebraic spaces over `B`, and let `c` be a
cocone for `D` in `Over B`. If `{family a}` is an fpqc covering of `c.pt.left`
such that each member `U_a` is the colimit of `X_i ×_X U_a` in `Over B` and
each overlap `U_a ×_X U_b` is the colimit of `X_i ×_X U_a ×_X U_b` in
`Over B`, then `c` is a colimit in `Over B`. -/
@[stacks 0GFQ]
theorem FpqcCovering.isColimit_of_fpqcCover {J : Type v} [Category.{v} J]
    {S : Scheme.{u}} {B : AlgebraicSpace S} (D : J ⥤ Over B) (c : Cocone D)
    {ι : Type w} (family : ι → Over c.pt.left) (hfamily : FpqcCovering family)
    (h_member : ∀ a, Nonempty (IsColimit (baseChangeCocone c (family a).hom)))
    (h_overlap :
      ∀ a b, Nonempty (IsColimit (baseChangeCocone c (overlapHom family a b)))) :
    Nonempty (IsColimit c) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
