module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over an open

The full subcategory of `Over W` on morphisms `g : X ⟶ W` that are proper
and for which the comparison `g⁻¹U ⟶ U` is an isomorphism.
-/

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsProperIsoOverOpen :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S},
    (X ⟶ Y) → ∀ (ι : U ⟶ Y) [IsOpenImmersion ι], Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isProperIsoOverOpen_iff :
  ∀ {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι],
    IsProperIsoOverOpen g ι ↔ Proper g ∧ IsIsoOverOpen g ι)

#check (AlgebraicGeometry.AlgebraicSpace.properIsoOverOpenProperty :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι], ObjectProperty (Over W))

#check (AlgebraicGeometry.AlgebraicSpace.properIsoOverOpenProperty_iff :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] (X : Over W),
    properIsoOverOpenProperty ι X ↔ IsProperIsoOverOpen X.hom ι)

#check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen.inclusion :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι], ProperIsoOverOpen ι ⥤ Over W)

#check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen.of :
  ∀ {S : Scheme.{u}} {W U Y : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι]
    (g : Y ⟶ W), IsProperIsoOverOpen g ι → ProperIsoOverOpen ι)

#check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen.instProper_hom :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : ProperIsoOverOpen ι), Proper X.obj.hom)

#check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen.instIsIso_openInverseImageTo :
  ∀ {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : ProperIsoOverOpen ι),
    IsIso (openInverseImageTo X.obj.hom ι))
