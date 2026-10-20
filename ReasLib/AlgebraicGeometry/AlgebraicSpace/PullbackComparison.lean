module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Geometric properties of fibre-product comparisons

For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of algebraic spaces over a
scheme, the canonical comparison `X ×_Z Y ⟶ X ×_T Y` is representable, locally of
finite type, locally quasi-finite, separated, and a monomorphism. Separation
properties of `h` imply stronger immersion and quasi-compactness properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representable. -/
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably locally of finite type. -/
theorem locallyOfFiniteType_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably separated. -/
theorem isSeparated_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably a monomorphism. -/
theorem monomorphisms_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a locally separated morphism
of algebraic spaces is an immersion. -/
instance isImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [LocallySeparated h] :
    IsImmersion (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a separated morphism of
algebraic spaces is a closed immersion. -/
instance isClosedImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    IsClosedImmersion (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a quasi-separated morphism
of algebraic spaces is representably quasi-compact. -/
theorem quasiCompact_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
