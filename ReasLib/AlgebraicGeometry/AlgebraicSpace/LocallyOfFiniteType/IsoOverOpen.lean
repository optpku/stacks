/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen

/-!
# Locally finite-type morphisms of algebraic spaces that are isomorphisms over an open

The full subcategory of `Over W` on morphisms `g : X ⟶ W` that are locally of
finite type and for which the comparison `g⁻¹U ⟶ U` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `g : X ⟶ Y` of algebraic spaces is locally of finite type and an
isomorphism over an open immersion `ι : U ⟶ Y` when `g` is locally of finite type
and `openInverseImageTo g ι : g⁻¹U ⟶ U` is an isomorphism. -/
def IsLocallyOfFiniteTypeIsoOverOpen {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] : Prop :=
  LocallyOfFiniteType g ∧ IsIsoOverOpen g ι

/-- `IsLocallyOfFiniteTypeIsoOverOpen g ι` is local finite type of `g` together with
`IsIsoOverOpen g ι`. -/
theorem isLocallyOfFiniteTypeIsoOverOpen_iff {S : Scheme.{u}}
    {X Y U : AlgebraicSpace S} (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] :
    IsLocallyOfFiniteTypeIsoOverOpen g ι ↔
      LocallyOfFiniteType g ∧ IsIsoOverOpen g ι :=
  Iff.rfl

/-- The object property on `Over W` selecting locally-of-finite-type morphisms that
are isomorphisms over the open immersion `ι`. -/
abbrev locallyOfFiniteTypeIsoOverOpenProperty {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : ObjectProperty (Over W) :=
  fun X ↦ IsLocallyOfFiniteTypeIsoOverOpen X.hom ι

/-- Membership in `locallyOfFiniteTypeIsoOverOpenProperty ι` is
`IsLocallyOfFiniteTypeIsoOverOpen` of the structure morphism. -/
theorem locallyOfFiniteTypeIsoOverOpenProperty_iff {S : Scheme.{u}}
    {W U : AlgebraicSpace S} (ι : U ⟶ W) [IsOpenImmersion ι] (X : Over W) :
    locallyOfFiniteTypeIsoOverOpenProperty ι X ↔
      IsLocallyOfFiniteTypeIsoOverOpen X.hom ι :=
  Iff.rfl

/-- The full subcategory of morphisms of algebraic spaces over `W` that are
locally of finite type and isomorphisms over the open immersion `ι`. -/
abbrev LocallyOfFiniteTypeIsoOverOpen {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] :=
  (locallyOfFiniteTypeIsoOverOpenProperty ι).FullSubcategory

namespace LocallyOfFiniteTypeIsoOverOpen

/-- The inclusion of `LocallyOfFiniteTypeIsoOverOpen ι` into the ambient slice
category `Over W`. -/
abbrev inclusion {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : LocallyOfFiniteTypeIsoOverOpen ι ⥤ Over W :=
  (locallyOfFiniteTypeIsoOverOpenProperty ι).ι

/-- A locally-of-finite-type morphism that is an isomorphism over `ι`, as an
object of `LocallyOfFiniteTypeIsoOverOpen ι`. -/
def of {S : Scheme.{u}} {W U Y : AlgebraicSpace S} (ι : U ⟶ W) [IsOpenImmersion ι]
    (g : Y ⟶ W) (hg : IsLocallyOfFiniteTypeIsoOverOpen g ι) :
    LocallyOfFiniteTypeIsoOverOpen ι where
  obj := Over.mk g
  property := hg

/-- The structure morphism of an object of `LocallyOfFiniteTypeIsoOverOpen ι` is
locally of finite type. -/
instance instLocallyOfFiniteType_hom {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : LocallyOfFiniteTypeIsoOverOpen ι) :
    LocallyOfFiniteType X.obj.hom :=
  X.property.1

/-- The comparison `g⁻¹U ⟶ U` of an object of `LocallyOfFiniteTypeIsoOverOpen ι`
is an isomorphism. -/
instance instIsIso_openInverseImageTo {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : LocallyOfFiniteTypeIsoOverOpen ι) :
    IsIso (openInverseImageTo X.obj.hom ι) :=
  X.property.2

end LocallyOfFiniteTypeIsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
