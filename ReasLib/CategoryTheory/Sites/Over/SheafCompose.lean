/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaf composition on slice sites

This leaf transports a sheaf-composition functor to the topology on a slice
category.  It keeps ringed-site and module-sheaf APIs from repeatedly carrying
the same slice-level composition evidence.
-/

@[expose] public section

universe uC vC uA vA uB vB

namespace CategoryTheory.GrothendieckTopology

/-- A functor that preserves sheaves after composition on a site also preserves sheaves after
composition on every slice site. -/
theorem hasSheafCompose_over
    {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C)
    {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B]
    (F : A ⥤ B) [J.HasSheafCompose F] (U : C) :
    (J.over U).HasSheafCompose F := sorry

/-- A functor that preserves sheaves after composition on a site has the same
property on every slice site. -/
instance HasSheafCompose.over
    {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C)
    {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B]
    (F : A ⥤ B) [J.HasSheafCompose F] (U : C) :
    (J.over U).HasSheafCompose F :=
  hasSheafCompose_over J F U

end CategoryTheory.GrothendieckTopology
