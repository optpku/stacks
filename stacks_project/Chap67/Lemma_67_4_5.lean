/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# The induced morphism of fibre products after a map of algebraic spaces

For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of algebraic spaces over a
scheme `S`, the comparison `pullback.mapDesc f g h : pullback f g ⟶ pullback (f ≫ h) (g ≫ h)`
is representable, locally of finite type, locally quasi-finite, separated, and a
monomorphism in the sense of Definition 65.5.1. If `h` is locally separated then it is
an immersion; if `h` is separated then it is a closed immersion; if `h` is
quasi-separated then it is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.4.5 (1): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h : pullback f g ⟶ pullback (f ≫ h) (g ≫ h)` is
representable. -/
@[stacks 03KN]
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (2): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is locally of finite type in the sense of
Definition 65.5.1. -/
@[stacks 03KN]
theorem locallyOfFiniteType_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (3): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is locally quasi-finite in the sense of
Definition 65.5.1. -/
@[stacks 03KN]
theorem locallyQuasiFinite_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (4): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is separated in the sense of Definition 65.5.1. -/
@[stacks 03KN]
theorem isSeparated_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (5): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is a monomorphism in the sense of Definition 65.5.1. -/
@[stacks 03KN]
theorem monomorphisms_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (6): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is locally
separated, then `pullback.mapDesc f g h` is an immersion. -/
@[stacks 03KN]
instance isImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [LocallySeparated h] :
    IsImmersion (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (7): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is separated, then
`pullback.mapDesc f g h` is a closed immersion. -/
@[stacks 03KN]
instance isClosedImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    IsClosedImmersion (pullback.mapDesc f g h) :=
  sorry

/-- Lemma 67.4.5 (8): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is quasi-separated,
then `pullback.mapDesc f g h` is quasi-compact in the sense of Definition 65.5.1. -/
@[stacks 03KN]
theorem quasiCompact_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
