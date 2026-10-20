/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural isomorphisms of total right-derived functors

An isomorphism of additive functors induces an isomorphism between any two specified total
right-derived models of those functors.  The localization and the two derived units remain
explicit, so this interface is suitable for transporting a site-level Beck--Chevalley
isomorphism without choosing representatives or inverses in a chapter file.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' vD w vH

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u} {D : Type u'} {H : Type w}
variable [Category.{v} C] [Category.{vD} D] [Category.{vH} H]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable {F F' : C ⥤ H} {RF RF' : D ⥤ H}
variable (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF')
variable [L.IsLocalization W]
variable [RF.IsRightDerivedFunctor α W]
variable [RF'.IsRightDerivedFunctor α' W]

/-- An underived natural isomorphism transported to specified total right-derived functors. -/
@[stacks 05T2 "transport of a natural isomorphism to total right-derived functors"]
noncomputable def natIsoOfIso (e : F ≅ F') : RF ≅ RF' :=
  RF.rightDerivedNatIso RF' α α' W e

/-- The forward map of `natIsoOfIso` is the derived map induced by the forward transformation. -/
@[simp, stacks 05T2 "forward derived map induced by a natural isomorphism"]
theorem natIsoOfIso_hom (e : F ≅ F') :
    (natIsoOfIso L W α α' e).hom =
      RF.rightDerivedNatTrans RF' α α' W e.hom := sorry

/-- The inverse map of `natIsoOfIso` is the derived map induced by the inverse transformation. -/
@[simp, stacks 05T2 "inverse derived map induced by a natural isomorphism"]
theorem natIsoOfIso_inv (e : F ≅ F') :
    (natIsoOfIso L W α α' e).inv =
      RF'.rightDerivedNatTrans RF α' α W e.inv := sorry

/-- An isomorphism class of underived functors transports to an isomorphism class of their
specified total right-derived models.  The proposition-valued interface avoids exposing a public
choice of a representative isomorphism. -/
@[stacks 05T2 "isomorphism classes of total right-derived functors"]
theorem isIsomorphic_of_isIsomorphic
    (L : C ⥤ D) (W : MorphismProperty C)
    (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF')
    (h : IsIsomorphic F F') : IsIsomorphic RF RF' := sorry


-- The isomorphism data are Mathlib's right-derived uniqueness construction; only its
-- naturality/specification laws remain deferred.

end CategoryTheory.Functor.RightDerived
