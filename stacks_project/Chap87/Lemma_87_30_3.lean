module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.PullbackComparison

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

/- Lemma 87.30.3 (1): The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representable by schemes. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.relativelyRepresentable_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    yoneda.relativelyRepresentable (pullback.mapDesc f g h))

/- Lemma 87.30.3 (2): The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably locally of finite type. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.locallyOfFiniteType_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (over (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 87.30.3 (3): The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably locally quasi-finite. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.locallyQuasiFinite_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (over (@AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 87.30.3 (4): The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably separated. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.isSeparated_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 87.30.3 (5): The canonical fibre-product comparison induced by a morphism of formal algebraic
spaces over a scheme is representably a monomorphism. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.monomorphisms_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T),
    (over (monomorphisms Scheme.{u})).presheaf (pullback.mapDesc f g h))

/- Lemma 87.30.3 (6): The canonical fibre-product comparison induced by a separated morphism of formal
algebraic spaces over a scheme is representably a closed immersion. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.isClosedImmersion_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h],
    (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

/- Lemma 87.30.3 (7): The canonical fibre-product comparison induced by a quasi-separated morphism of
formal algebraic spaces over a scheme is representably quasi-compact. -/
@[stacks 0ARQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.quasiCompact_mapDesc :
  ∀ {S : Scheme.{u}} {X Y Z T : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace T]
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h],
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h))

end AlgebraicGeometry.FormalAlgebraicSpace
