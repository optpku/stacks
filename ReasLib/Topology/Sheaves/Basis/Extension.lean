/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Topology.Sheaves.Basis.Basic

/-!
# Extensions of presheaves from a collection of opens

This module contains the coefficient-category-independent data of extending a presheaf on a
collection of opens to a sheaf on the ambient space.  It intentionally makes no basis or sheaf
condition assumption: those assumptions belong to the comparison results that construct such an
extension.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace BasisPresheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}
variable {C : Type v} [Category.{w} C]

/-- An extension of a presheaf on the opens in `B` consists of a sheaf on `X` and an explicit
identification of its restriction along `basisOpenInclusion B` with the original presheaf. -/
structure Extension (P : (BasisOpen B)ᵒᵖ ⥤ C) where
  /-- The extending sheaf on the ambient topological space. -/
  sheaf : TopCat.Sheaf C X
  /-- The specified identification after restricting the extension to the chosen opens. -/
  restrictIso : P ≅ (basisOpenInclusion B).op ⋙ sheaf.presheaf

/-- An isomorphism between two extensions is compatible when its restriction intertwines their
specified identifications with the original presheaf. -/
def Extension.IsCompatibleIso {P : (BasisOpen B)ᵒᵖ ⥤ C}
    (E G : Extension P) (e : E.sheaf ≅ G.sheaf) : Prop :=
  E.restrictIso.hom ≫ Functor.whiskerLeft (basisOpenInclusion B).op e.hom.1 =
    G.restrictIso.hom

end BasisPresheaf
