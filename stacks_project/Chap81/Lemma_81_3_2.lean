/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Colimit
public import stacks_project.Chap81.Lemma_81_3_2_Pullback
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

/- Lemma 81.3.2: A cocone of algebraic spaces over `B` is colimiting if its
canonical base changes to members and pairwise overlaps of an fpqc covering
of its apex are colimiting in `Over B`. -/
@[stacks 0GFQ] #check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.isColimit_of_fpqcCover :
  ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
    (D : J ⥤ Over B) (c : Cocone D) {ι : Type w}
    (family : ι → Over c.pt.left) (hfamily : FpqcCovering family)
    (h_member : ∀ a, Nonempty (IsColimit (baseChangeCocone c (family a).hom)))
    (h_overlap :
      ∀ a b, Nonempty (IsColimit (baseChangeCocone c (overlapHom family a b)))),
    Nonempty (IsColimit c))
