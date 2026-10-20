/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen

/-!
# Finite-presentation morphisms of algebraic spaces that are isomorphisms over an open

The full subcategory of `Over W` on morphisms `g : X ⟶ W` of finite presentation
for which the comparison `g⁻¹U ⟶ U` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `g : X ⟶ Y` of algebraic spaces is of finite presentation and an
isomorphism over an open immersion `ι : U ⟶ Y` when `g` is of finite presentation
and `openInverseImageTo g ι : g⁻¹U ⟶ U` is an isomorphism. -/
def IsFinitePresentationIsoOverOpen {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] : Prop :=
  FinitePresentation g ∧ IsIsoOverOpen g ι

/-- `IsFinitePresentationIsoOverOpen g ι` is finite presentation of `g` together with
`IsIsoOverOpen g ι`. -/
theorem isFinitePresentationIsoOverOpen_iff {S : Scheme.{u}}
    {X Y U : AlgebraicSpace S} (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] :
    IsFinitePresentationIsoOverOpen g ι ↔
      FinitePresentation g ∧ IsIsoOverOpen g ι :=
  sorry

/-- The object property on `Over W` selecting finite-presentation morphisms that are
isomorphisms over the open immersion `ι`. -/
abbrev finitePresentationIsoOverOpenProperty {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : ObjectProperty (Over W) :=
  fun X ↦ IsFinitePresentationIsoOverOpen X.hom ι

/-- Membership in `finitePresentationIsoOverOpenProperty ι` is
`IsFinitePresentationIsoOverOpen` of the structure morphism. -/
theorem finitePresentationIsoOverOpenProperty_iff {S : Scheme.{u}}
    {W U : AlgebraicSpace S} (ι : U ⟶ W) [IsOpenImmersion ι] (X : Over W) :
    finitePresentationIsoOverOpenProperty ι X ↔
      IsFinitePresentationIsoOverOpen X.hom ι :=
  sorry

/-- The full subcategory of morphisms of algebraic spaces over `W` that are of
finite presentation and isomorphisms over the open immersion `ι`. -/
abbrev FinitePresentationIsoOverOpen {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] :=
  (finitePresentationIsoOverOpenProperty ι).FullSubcategory

namespace FinitePresentationIsoOverOpen

/-- The inclusion of `FinitePresentationIsoOverOpen ι` into the ambient slice
category `Over W`. -/
abbrev inclusion {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : FinitePresentationIsoOverOpen ι ⥤ Over W :=
  (finitePresentationIsoOverOpenProperty ι).ι

/-- A finite-presentation morphism that is an isomorphism over `ι`, as an object of
`FinitePresentationIsoOverOpen ι`. -/
def of {S : Scheme.{u}} {W U Y : AlgebraicSpace S} (ι : U ⟶ W) [IsOpenImmersion ι]
    (g : Y ⟶ W) (hg : IsFinitePresentationIsoOverOpen g ι) :
    FinitePresentationIsoOverOpen ι where
  obj := Over.mk g
  property := hg

/-- The structure morphism of an object of `FinitePresentationIsoOverOpen ι` is of
finite presentation. -/
instance instFinitePresentation_hom {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : FinitePresentationIsoOverOpen ι) :
    FinitePresentation X.obj.hom :=
  X.property.1

/-- The comparison `g⁻¹U ⟶ U` of an object of `FinitePresentationIsoOverOpen ι` is an
isomorphism. -/
instance instIsIso_openInverseImageTo {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : FinitePresentationIsoOverOpen ι) :
    IsIso (openInverseImageTo X.obj.hom ι) :=
  X.property.2

end FinitePresentationIsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
