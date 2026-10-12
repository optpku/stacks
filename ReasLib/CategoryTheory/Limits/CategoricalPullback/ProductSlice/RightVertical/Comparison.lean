/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Legs
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal

/-!
# Comparison with the transported diagonal functor

This file identifies the explicit product-slice right-vertical functor with the functor obtained
from the product-slice and leg-change equivalences followed by `CategoricalPullback.toDiagonal`.
-/

@[expose] public section

universe vC vXS uC uXS

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace Limits.CategoricalPullback.ProductSlice

section RightVertical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type uC} [Category.{vC} C] [Limits.HasBinaryProducts C]
variable {XS : Type uXS} [Category.{vXS} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

namespace RightVertical.Implementation

/-- Compatibility of the identity leg isomorphisms used in the product-slice right-vertical
comparison. -/
private theorem comparisonComponent_comm
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    let source := (CategoricalPullback.ProductSlice.fromProduct U V ⋙
      (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
        CategoricalPullback.toDiagonal gU gV xp).obj c
    let target := (RightVertical.functor (RightVertical.baseIso eU eV)).obj c
    xp.map (𝟙 source.fst) ≫ target.iso.hom =
      source.iso.hom ≫ xp.map (𝟙 source.snd) := sorry
/- Proof strategy: unfold the product-of-slices equivalence and leg congruence, use
`CategoricalPullback.toDiagonal.obj.iso.hom`, and cancel identities. -/

/-- The objectwise isomorphism identifying the transported diagonal functor with the explicit
product-slice right vertical. -/
private noncomputable def comparisonComponent
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    (CategoricalPullback.ProductSlice.fromProduct U V ⋙
        (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
          CategoricalPullback.toDiagonal gU gV xp).obj c ≅
      (RightVertical.functor (RightVertical.baseIso eU eV)).obj c :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    (comparisonComponent_comm eU eV c)

/-- Naturality of the objectwise right-vertical comparison. -/
private theorem comparisonNaturality
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    (CategoricalPullback.ProductSlice.fromProduct U V ⋙
        (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
          CategoricalPullback.toDiagonal gU gV xp).map f ≫
        (comparisonComponent eU eV d).hom =
      (comparisonComponent eU eV c).hom ≫
        (RightVertical.functor (RightVertical.baseIso eU eV)).map f := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both projection equations reduce to
functoriality of `Over.map` and the two leg functors. -/

end RightVertical.Implementation

/-- The transported categorical diagonal comparison with the explicit product-slice right
vertical. -/
noncomputable def RightVertical.comparisonIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    CategoricalPullback.ProductSlice.fromProduct U V ⋙
        (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
          CategoricalPullback.toDiagonal gU gV xp ≅
      RightVertical.functor (RightVertical.baseIso eU eV) :=
  NatIso.ofComponents
    (RightVertical.Implementation.comparisonComponent eU eV)
    (RightVertical.Implementation.comparisonNaturality eU eV)

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
