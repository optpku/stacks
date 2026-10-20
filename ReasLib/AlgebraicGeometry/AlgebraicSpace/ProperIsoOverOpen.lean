module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over an open

The full subcategory of `Over W` on morphisms `g : X ⟶ W` that are proper
and for which the comparison `g⁻¹U ⟶ U` is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `g : X ⟶ Y` of algebraic spaces is proper and an isomorphism
over an open immersion `ι : U ⟶ Y` when `g` is proper and
`openInverseImageTo g ι : g⁻¹U ⟶ U` is an isomorphism. -/
def IsProperIsoOverOpen {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] : Prop :=
  Proper g ∧ IsIsoOverOpen g ι

/-- `IsProperIsoOverOpen g ι` is properness of `g` together with
`IsIsoOverOpen g ι`. -/
theorem isProperIsoOverOpen_iff {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] :
    IsProperIsoOverOpen g ι ↔ Proper g ∧ IsIsoOverOpen g ι :=
  sorry

/-- The object property on `Over W` selecting proper morphisms that are
isomorphisms over the open immersion `ι`. -/
abbrev properIsoOverOpenProperty {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : ObjectProperty (Over W) :=
  fun X ↦ IsProperIsoOverOpen X.hom ι

/-- Membership in `properIsoOverOpenProperty ι` is `IsProperIsoOverOpen` of
the structure morphism. -/
theorem properIsoOverOpenProperty_iff {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] (X : Over W) :
    properIsoOverOpenProperty ι X ↔ IsProperIsoOverOpen X.hom ι :=
  sorry

/-- The full subcategory of morphisms of algebraic spaces over `W` that are
proper and isomorphisms over the open immersion `ι`. -/
abbrev ProperIsoOverOpen {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] :=
  (properIsoOverOpenProperty ι).FullSubcategory

namespace ProperIsoOverOpen

/-- The inclusion of `ProperIsoOverOpen ι` into the ambient slice category
`Over W`. -/
abbrev inclusion {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : ProperIsoOverOpen ι ⥤ Over W :=
  (properIsoOverOpenProperty ι).ι

/-- A proper morphism that is an isomorphism over `ι`, as an object of
`ProperIsoOverOpen ι`. -/
def of {S : Scheme.{u}} {W U Y : AlgebraicSpace S} (ι : U ⟶ W) [IsOpenImmersion ι]
    (g : Y ⟶ W) (hg : IsProperIsoOverOpen g ι) :
    ProperIsoOverOpen ι where
  obj := Over.mk g
  property := hg

/-- The structure morphism of an object of `ProperIsoOverOpen ι` is proper. -/
instance instProper_hom {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : ProperIsoOverOpen ι) :
    Proper X.obj.hom :=
  X.property.1

/-- The comparison `g⁻¹U ⟶ U` of an object of `ProperIsoOverOpen ι` is an
isomorphism. -/
instance instIsIso_openInverseImageTo {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : ProperIsoOverOpen ι) :
    IsIso (openInverseImageTo X.obj.hom ι) :=
  X.property.2

end ProperIsoOverOpen

end AlgebraicGeometry.AlgebraicSpace
