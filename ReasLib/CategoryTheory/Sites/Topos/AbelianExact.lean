/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Exactness of abelian inverse image under geometric morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{w})]
variable (f : MorphismOfTopoiIn.{u, u', v, v', w} J K)

/-- Abelian inverse image under a geometric morphism preserves finite limits. -/
instance abelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits f.abelianInverseImage := sorry

/-- Abelian inverse image under a geometric morphism preserves finite colimits. -/
instance abelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits f.abelianInverseImage := sorry

/-- Abelian inverse image under a geometric morphism is additive. -/
instance abelianInverseImage_additive : f.abelianInverseImage.Additive := sorry

end CategoryTheory.MorphismOfTopoiIn
