module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Cocone

/-!
# Colimits local for fpqc coverings

A cocone of algebraic spaces is colimiting if its canonical base changes to
members and pairwise overlaps of an fpqc covering of its apex are colimiting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- A cocone of algebraic spaces over `B` is colimiting if its canonical base
changes to every member and every pairwise overlap of an fpqc covering of its
apex are colimiting in `Over B`. -/
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
