/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v z

namespace CategoryTheory.AbelianSheaf

/-- On a site bounded by the coefficient universe, sheafification inverts exactly
the locally bijective morphisms of additive presheaves. -/
instance wEqualsLocallyBijective_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{max u v, z}] : J.WEqualsLocallyBijective AddCommGrpCat.{z} := by
  have hSmall : Small.{z} C :=
    @Small.trans_univLE.{max u v, z, u} C (small_max.{v} C) inferInstance
  have hLocal : LocallySmall.{z} C :=
    ⟨fun U V => @Small.trans_univLE.{max u v, z, v} (U ⟶ V)
      (small_max.{u} (U ⟶ V)) inferInstance⟩
  have hEssential : EssentiallySmall.{z} C :=
    @essentiallySmall_of_small_of_locallySmall _ _ hSmall hLocal
  have hLimits : ∀ V : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (equivSmallModel.{z} C).inverse.op)
        AddCommGrpCat.{z} := fun _ => HasLimitsOfShape.of_small _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

/-- Additive sheaves on a site bounded by the coefficient universe form a
Grothendieck abelian category in that universe. -/
instance isGrothendieckAbelian_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{max u v, z}] [HasSheafify J AddCommGrpCat.{z}] :
    IsGrothendieckAbelian.{z} (Sheaf J AddCommGrpCat.{z}) := sorry

end CategoryTheory.AbelianSheaf
