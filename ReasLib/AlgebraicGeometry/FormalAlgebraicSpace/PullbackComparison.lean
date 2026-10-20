module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Pullback

/-!
# The induced morphism of fibre products after a map of formal algebraic spaces

For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of formal algebraic
spaces over a scheme `S`, the comparison
`pullback.mapDesc f g h : pullback f g ⟶ pullback (f ≫ h) (g ≫ h)` is
representable by schemes, locally of finite type, locally quasi-finite,
separated, and a monomorphism. If `h` is separated then it is a closed
immersion; if `h` is quasi-separated then it is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representable by schemes. -/
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably locally of finite type. -/
theorem locallyOfFiniteType_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably locally quasi-finite. -/
theorem locallyQuasiFinite_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably separated. -/
theorem isSeparated_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably a monomorphism. -/
theorem monomorphisms_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (monomorphisms Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a separated morphism of formal
algebraic spaces over a scheme is representably a closed immersion. -/
theorem isClosedImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- The canonical fibre-product comparison induced by a quasi-separated morphism of
formal algebraic spaces over a scheme is representably quasi-compact. -/
theorem quasiCompact_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
