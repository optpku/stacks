module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackComparison

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

/- Lemma 67.4.5 (1): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h : pullback f g ⟶ pullback (f ≫ h) (g ≫ h)` is
representable. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    yoneda.relativelyRepresentable (pullback.mapDesc f g h))

/- Lemma 67.4.5 (2): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is locally of finite type in the sense of
Definition 65.5.1. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h))

/- Lemma 67.4.5 (3): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is locally quasi-finite in the sense of
Definition 65.5.1. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 67.4.5 (4): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is separated in the sense of Definition 65.5.1. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.isSeparated_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h))

/- Lemma 67.4.5 (5): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. The induced morphism
`pullback.mapDesc f g h` is a monomorphism in the sense of Definition 65.5.1. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.monomorphisms_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 67.4.5 (6): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is locally
separated, then `pullback.mapDesc f g h` is an immersion. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.isImmersion_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [LocallySeparated h],
    IsImmersion (pullback.mapDesc f g h))

/- Lemma 67.4.5 (7): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is separated, then
`pullback.mapDesc f g h` is a closed immersion. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h],
    IsClosedImmersion (pullback.mapDesc f g h))

/- Lemma 67.4.5 (8): let `S` be a scheme and let `f : X ⟶ Z`, `g : Y ⟶ Z`, and
`h : Z ⟶ T` be morphisms of algebraic spaces over `S`. If `h` is quasi-separated,
then `pullback.mapDesc f g h` is quasi-compact in the sense of Definition 65.5.1. -/
@[stacks 03KN] #check (AlgebraicGeometry.AlgebraicSpace.quasiCompact_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h],
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h))

end AlgebraicGeometry.AlgebraicSpace
