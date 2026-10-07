module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_21_1_Formal

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

/-- Lemma 87.30.3 (1): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. The induced
morphism `pullback.mapDesc f g h : pullback f g ⟶ pullback (f ≫ h) (g ≫ h)` is
representable by schemes. -/
@[stacks 0ARQ]
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (2): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. The induced
morphism `pullback.mapDesc f g h` is locally of finite type. -/
@[stacks 0ARQ]
theorem locallyOfFiniteType_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (3): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. The induced
morphism `pullback.mapDesc f g h` is locally quasi-finite. -/
@[stacks 0ARQ]
theorem locallyQuasiFinite_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (4): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. The induced
morphism `pullback.mapDesc f g h` is separated. -/
@[stacks 0ARQ]
theorem isSeparated_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (5): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. The induced
morphism `pullback.mapDesc f g h` is a monomorphism. -/
@[stacks 0ARQ]
theorem monomorphisms_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (over (monomorphisms Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (6): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. If `h` is
separated, then `pullback.mapDesc f g h` is a closed immersion. -/
@[stacks 0ARQ]
theorem isClosedImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 87.30.3 (7): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of formal algebraic spaces over `S`. If `h` is
quasi-separated, then `pullback.mapDesc f g h` is quasi-compact. -/
@[stacks 0ARQ]
theorem quasiCompact_mapDesc {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
