/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Support

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Sections supported on a closed subscheme, regarded as ambient étale sheaves, form
the kernel of the unit of restriction to the open complement. -/
def onAmbient : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (Abelian.adjunction (closedImmersionComplement i).ι).unit

/-- Sections supported on a closed subscheme are realized on its small étale site
by inverse image of their ambient realization. -/
def onClosed : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  onAmbient i ⋙ Abelian.inverseImage i

/-- Taking ambient sections with closed support is additive. -/
instance onAmbient_additive : (onAmbient i).Additive := sorry

/-- Taking sections with closed support is additive. -/
instance onClosed_additive : (onClosed i).Additive := sorry

/-- Taking sections with closed support preserves finite limits. -/
instance onClosed_preservesFiniteLimits : PreservesFiniteLimits (onClosed i) := sorry

/-- Direct image along a closed immersion preserves finite colimits. -/
instance closedImage_preservesFiniteColimits :
    PreservesFiniteColimits (Abelian.directImage i) := sorry

/-- The unit of closed inverse image is invertible on ambient sections with support. -/
instance ambientUnit_isIso :
    IsIso (whiskerLeft (onAmbient i) (Abelian.adjunction i).unit) := sorry

/-- Closed direct image identifies the closed and ambient realizations of support. -/
def pushforwardIso : onClosed i ⋙ Abelian.directImage i ≅ onAmbient i :=
  (asIso (whiskerLeft (onAmbient i) (Abelian.adjunction i).unit)).symm

/-- Closed-supported sections include naturally into the ambient sheaf. -/
def inclusion : onClosed i ⋙ Abelian.directImage i ⟶
    𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (pushforwardIso i).hom ≫ kernel.ι (Abelian.adjunction (closedImmersionComplement i).ι).unit

/-- Restricting the inclusion of closed-supported sections to the complement gives zero. -/
theorem inclusion_comp_unit : inclusion i ≫
    (Abelian.adjunction (closedImmersionComplement i).ι).unit = 0 := sorry

/-- Restriction to the complementary open subscheme preserves injective sheaves. -/
instance inverseImage_injective (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Injective I] :
    Injective ((Abelian.inverseImage (closedImmersionComplement i).ι).obj I) := sorry

/-- The complementary restriction unit of an injective étale sheaf is epimorphic. -/
instance restrictionUnit_epi (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Injective I] :
    Epi ((Abelian.adjunction (closedImmersionComplement i).ι).unit.app I) := sorry

end AlgebraicGeometry.Scheme.Etale.Support
