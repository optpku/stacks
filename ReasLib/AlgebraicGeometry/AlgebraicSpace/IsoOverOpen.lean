module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage

/-!
# Morphisms of algebraic spaces that are isomorphisms over an open

The full subcategory of `Over W` on morphisms `g : X ⟶ W` for which the
comparison `g⁻¹U ⟶ U` is an isomorphism. The closed-complement
specialization is the same property on `W \ T`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `g : X ⟶ Y` of algebraic spaces is an isomorphism over an open
immersion `ι : U ⟶ Y` when `openInverseImageTo g ι : g⁻¹U ⟶ U` is an
isomorphism. -/
def IsIsoOverOpen {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] : Prop :=
  IsIso (openInverseImageTo g ι)

/-- `IsIsoOverOpen g ι` is the assertion that `openInverseImageTo g ι` is an
isomorphism. -/
theorem isIsoOverOpen_iff {S : Scheme.{u}} {X Y U : AlgebraicSpace S}
    (g : X ⟶ Y) (ι : U ⟶ Y) [IsOpenImmersion ι] :
    IsIsoOverOpen g ι ↔ IsIso (openInverseImageTo g ι) :=
  sorry

/-- The object property on `Over W` selecting morphisms that are isomorphisms
over the open immersion `ι`. -/
abbrev isoOverOpenProperty {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : ObjectProperty (Over W) :=
  fun X ↦ IsIsoOverOpen X.hom ι

/-- Membership in `isoOverOpenProperty ι` is `IsIsoOverOpen` of the structure
morphism. -/
theorem isoOverOpenProperty_iff {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] (X : Over W) :
    isoOverOpenProperty ι X ↔ IsIsoOverOpen X.hom ι :=
  sorry

/-- The full subcategory of morphisms of algebraic spaces over `W` that are
isomorphisms over the open immersion `ι`. -/
abbrev IsoOverOpen {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] :=
  (isoOverOpenProperty ι).FullSubcategory

namespace IsoOverOpen

/-- The inclusion of `IsoOverOpen ι` into the ambient slice category `Over W`. -/
abbrev inclusion {S : Scheme.{u}} {W U : AlgebraicSpace S}
    (ι : U ⟶ W) [IsOpenImmersion ι] : IsoOverOpen ι ⥤ Over W :=
  (isoOverOpenProperty ι).ι

/-- The comparison `g⁻¹U ⟶ U` of an object of `IsoOverOpen ι` is an
isomorphism. -/
instance instIsIso_openInverseImageTo {S : Scheme.{u}} {W U : AlgebraicSpace S}
    {ι : U ⟶ W} [IsOpenImmersion ι] (X : IsoOverOpen ι) :
    IsIso (openInverseImageTo X.obj.hom ι) :=
  X.property

end IsoOverOpen

/-- The full subcategory of morphisms over `W` that are isomorphisms over the
open complement of a closed immersion `i : T ⟶ W`. -/
abbrev IsoOverComplement {S : Scheme.{u}} {W T : AlgebraicSpace S}
    (i : T ⟶ W) [IsClosedImmersion i] :=
  IsoOverOpen (closedImmersionComplementι i)

/-- `IsoOverComplement i` is `IsoOverOpen` of the complement immersion of `i`. -/
theorem isoOverComplement_eq {S : Scheme.{u}} {W T : AlgebraicSpace S}
    (i : T ⟶ W) [IsClosedImmersion i] :
    IsoOverComplement i = IsoOverOpen (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
