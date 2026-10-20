/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Affine
import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

/- Definition 96.24.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. The associated affine site is the full subcategory `𝒳_affine` of
`𝒳` whose objects are those `x` lying over an affine scheme `U`. The topology
on `𝒳_affine` is the chaotic one, i.e. sheaves on `𝒳_affine` are the same as
presheaves. -/
@[stacks 0H09] #check (AlgebraicGeometry.GroupoidsOver.affineTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (((Scheme.affineOverProperty S).inverseImage X.p).FullSubcategory))

#check (AlgebraicGeometry.GroupoidsOver.affineInclusion :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    AlgebraicGeometry.GroupoidsOver.Affine X ⥤ X.total)

section

variable {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
  (A : Type w) [Category.{u} A]

#check (CategoryTheory.sheafBotEquivalence A :
  Sheaf (AlgebraicGeometry.GroupoidsOver.affineTopology X) A ≌
    (AlgebraicGeometry.GroupoidsOver.Affine X)ᵒᵖ ⥤ A)

end
