module

public import stacks_project.Chap92.«92_28_0_1_Transitivity»
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Fibre-product cone of cotangent complexes of algebraic spaces

For morphisms `X ⟶ B` and `Y ⟶ B` of algebraic spaces over a scheme `S`, this module
owns the object `E` of `D(O_W)` obtained as the mapping cone of the sum of the two
first transitivity maps
`Lp^* L_{X/B} ⊕ Lq^* L_{Y/B} ⟶ L_{W/B}`
on `W = X ×_B Y`, together with the comparison maps filling the fibre-product diagram.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CochainComplex
open HomologicalComplex
open ComplexShape
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

variable {S : Scheme.{u}}
variable {B X Y : AlgebraicSpace S}

/-- The structure morphism `X ×_B Y ⟶ B` of a fibre product of algebraic spaces. -/
abbrev toBase (f : X ⟶ B) (g : Y ⟶ B) : pullback f g ⟶ B :=
  pullback.fst f g ≫ f

/-- Identification of `L_{W/B}` along `pullback.condition`. -/
def cotangentToBaseIso (f : X ⟶ B) (g : Y ⟶ B) :
    cotangentCochain (pullback.snd f g ≫ g) ≅ cotangentCochain (toBase f g) :=
  eqToIso (congrArg cotangentCochain pullback.condition.symm)

/-- The cochain-level sum of the two first transitivity maps into `L_{W/B}`. -/
def sumMapCochain (f : X ⟶ B) (g : Y ⟶ B) :
    (pullbackCotangentCochain (pullback.fst f g) f ⊞
        pullbackCotangentCochain (pullback.snd f g) g) ⟶
      cotangentCochain (toBase f g) :=
  biprod.desc
    (transitivityMapCochain (pullback.fst f g) f ≫
      (compositeToBaseIso (pullback.fst f g) f).hom)
    (transitivityMapCochain (pullback.snd f g) g ≫
      (compositeToBaseIso (pullback.snd f g) g).hom ≫ (cotangentToBaseIso f g).hom)

/-- Unfolding of `sumMapCochain` as `biprod.desc` of the two first transitivity maps. -/
theorem sumMapCochain_eq (f : X ⟶ B) (g : Y ⟶ B) :
    sumMapCochain f g =
      biprod.desc
        (transitivityMapCochain (pullback.fst f g) f ≫
          (compositeToBaseIso (pullback.fst f g) f).hom)
        (transitivityMapCochain (pullback.snd f g) g ≫
          (compositeToBaseIso (pullback.snd f g) g).hom ≫
            (cotangentToBaseIso f g).hom) :=
  sorry

/-- The left inclusion into the biproduct recovers the first transitivity map along `p`. -/
theorem sumMapCochain_inl (f : X ⟶ B) (g : Y ⟶ B) :
    biprod.inl ≫ sumMapCochain f g =
      transitivityMapCochain (pullback.fst f g) f ≫
        (compositeToBaseIso (pullback.fst f g) f).hom :=
  sorry

/-- The right inclusion into the biproduct recovers the first transitivity map along `q`. -/
theorem sumMapCochain_inr (f : X ⟶ B) (g : Y ⟶ B) :
    biprod.inr ≫ sumMapCochain f g =
      transitivityMapCochain (pullback.snd f g) g ≫
        (compositeToBaseIso (pullback.snd f g) g).hom ≫ (cotangentToBaseIso f g).hom :=
  sorry

/-- The derived-level sum of the two first transitivity maps. -/
def sumMap (f : X ⟶ B) (g : Y ⟶ B) :
    DerivedCategory.Q.obj
        (pullbackCotangentCochain (pullback.fst f g) f ⊞
          pullbackCotangentCochain (pullback.snd f g) g) ⟶
      cotangent (toBase f g) :=
  DerivedCategory.Q.map (sumMapCochain f g)

/-- Unfolding of `sumMap` as `DerivedCategory.Q.map` of `sumMapCochain`. -/
theorem sumMap_eq (f : X ⟶ B) (g : Y ⟶ B) :
    sumMap f g = DerivedCategory.Q.map (sumMapCochain f g) :=
  sorry

/-- The cochain-level object `E` filling the upper-right corner of the fibre-product
diagram. -/
def coneCochain (f : X ⟶ B) (g : Y ⟶ B) : CochainComplex (CommModules (pullback f g)) ℤ :=
  mappingCone (sumMapCochain f g)

/-- Unfolding of `coneCochain` as a mapping cone. -/
theorem coneCochain_eq (f : X ⟶ B) (g : Y ⟶ B) :
    coneCochain f g = mappingCone (sumMapCochain f g) :=
  sorry

/-- The object `E` of `D(𝒪_{X ×_B Y})` filling the upper-right corner of the fibre-product
diagram of cotangent complexes. -/
def cone (f : X ⟶ B) (g : Y ⟶ B) : DerivedCategory (CommModules (pullback f g)) :=
  DerivedCategory.Q.obj (coneCochain f g)

/-- Unfolding of `cone` as `DerivedCategory.Q` of the mapping cone of `sumMapCochain`. -/
theorem cone_eq (f : X ⟶ B) (g : Y ⟶ B) :
    cone f g = DerivedCategory.Q.obj (coneCochain f g) :=
  sorry

/-- The canonical map `L_{W/B} ⟶ E` induced by `mappingCone.inr`. -/
def coneInr (f : X ⟶ B) (g : Y ⟶ B) :
    cotangent (toBase f g) ⟶ cone f g :=
  DerivedCategory.Q.map (mappingCone.inr (sumMapCochain f g))

/-- Unfolding of `coneInr` as `DerivedCategory.Q.map` of `mappingCone.inr`. -/
theorem coneInr_eq (f : X ⟶ B) (g : Y ⟶ B) :
    coneInr f g = DerivedCategory.Q.map (mappingCone.inr (sumMapCochain f g)) :=
  sorry

/-- The first arrow of the top row, `Lp^* L_{X/B} ⟶ L_{W/Y}`. -/
def topMap (f : X ⟶ B) (g : Y ⟶ B) :
    pullbackCotangent (pullback.fst f g) f ⟶ cotangent (pullback.snd f g) :=
  transitivityMap (pullback.fst f g) f ≫
    DerivedCategory.Q.map (cotangentToBaseIso f g).inv ≫
    toRelativeMap (pullback.snd f g) g

/-- Unfolding of `topMap` as the composite through `L_{W/B}`. -/
theorem topMap_eq (f : X ⟶ B) (g : Y ⟶ B) :
    topMap f g =
      transitivityMap (pullback.fst f g) f ≫
        DerivedCategory.Q.map (cotangentToBaseIso f g).inv ≫
        toRelativeMap (pullback.snd f g) g :=
  sorry

/-- The first arrow of the right column, `Lq^* L_{Y/B} ⟶ L_{W/X}`. -/
def rightMap (f : X ⟶ B) (g : Y ⟶ B) :
    pullbackCotangent (pullback.snd f g) g ⟶ cotangent (pullback.fst f g) :=
  transitivityMap (pullback.snd f g) g ≫
    DerivedCategory.Q.map (cotangentToBaseIso f g).hom ≫
    toRelativeMap (pullback.fst f g) f

/-- Unfolding of `rightMap` as the composite through `L_{W/B}`. -/
theorem rightMap_eq (f : X ⟶ B) (g : Y ⟶ B) :
    rightMap f g =
      transitivityMap (pullback.snd f g) g ≫
        DerivedCategory.Q.map (cotangentToBaseIso f g).hom ≫
        toRelativeMap (pullback.fst f g) f :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inl`. -/
theorem fromOverX_comm (f : X ⟶ B) (g : Y ⟶ B) :
    transitivityMapCochain (pullback.fst f g) f ≫
        (compositeToBaseIso (pullback.fst f g) f).hom =
      biprod.inl ≫ sumMapCochain f g :=
  sorry

/-- Commutativity of the square used to induce a map of mapping cones along `biprod.inr`. -/
theorem fromOverY_comm (f : X ⟶ B) (g : Y ⟶ B) :
    transitivityMapCochain (pullback.snd f g) g ≫
        (compositeToBaseIso (pullback.snd f g) g).hom ≫ (cotangentToBaseIso f g).hom =
      biprod.inr ≫ sumMapCochain f g :=
  sorry

/-- The cochain-level TR3 map from the mapping cone of the first transitivity map along `p`
into the cone of `sumMapCochain`. -/
def fromOverXCochain (f : X ⟶ B) (g : Y ⟶ B) :
    mappingCone (transitivityMapCochain (pullback.fst f g) f) ⟶ coneCochain f g :=
  mappingCone.map (transitivityMapCochain (pullback.fst f g) f) (sumMapCochain f g)
    biprod.inl (compositeToBaseIso (pullback.fst f g) f).hom (fromOverX_comm f g)

/-- The derived-level TR3 map from the mapping-cone model of `L_{W/X}` into `E`. -/
def fromOverX (f : X ⟶ B) (g : Y ⟶ B) :
    DerivedCategory.Q.obj (mappingCone (transitivityMapCochain (pullback.fst f g) f)) ⟶
      cone f g :=
  DerivedCategory.Q.map (fromOverXCochain f g)

/-- Unfolding of `fromOverX` as `DerivedCategory.Q.map` of the cochain TR3 map. -/
theorem fromOverX_eq (f : X ⟶ B) (g : Y ⟶ B) :
    fromOverX f g = DerivedCategory.Q.map (fromOverXCochain f g) :=
  sorry

/-- The cochain-level TR3 map from the mapping cone of the first transitivity map along `q`
into the cone of `sumMapCochain`. -/
def fromOverYCochain (f : X ⟶ B) (g : Y ⟶ B) :
    mappingCone (transitivityMapCochain (pullback.snd f g) g) ⟶ coneCochain f g :=
  mappingCone.map (transitivityMapCochain (pullback.snd f g) g) (sumMapCochain f g)
    biprod.inr
      ((compositeToBaseIso (pullback.snd f g) g).hom ≫ (cotangentToBaseIso f g).hom)
      (fromOverY_comm f g)

/-- The derived-level TR3 map from the mapping-cone model of `L_{W/Y}` into `E`. -/
def fromOverY (f : X ⟶ B) (g : Y ⟶ B) :
    DerivedCategory.Q.obj (mappingCone (transitivityMapCochain (pullback.snd f g) g)) ⟶
      cone f g :=
  DerivedCategory.Q.map (fromOverYCochain f g)

/-- Unfolding of `fromOverY` as `DerivedCategory.Q.map` of the cochain TR3 map. -/
theorem fromOverY_eq (f : X ⟶ B) (g : Y ⟶ B) :
    fromOverY f g = DerivedCategory.Q.map (fromOverYCochain f g) :=
  sorry

/-- The diagram arrow `L_{W/X} ⟶ E`, as `DerivedCategory.Q.map` of
`toMappingConeCochain` composed with `fromOverXCochain`. -/
def toConeFromOverX (f : X ⟶ B) (g : Y ⟶ B) :
    cotangent (pullback.fst f g) ⟶ cone f g :=
  DerivedCategory.Q.map
    (toMappingConeCochain (pullback.fst f g) f ≫ fromOverXCochain f g)

/-- Unfolding of `toConeFromOverX` as `DerivedCategory.Q.map` of the composite
`toMappingConeCochain ≫ fromOverXCochain`. -/
theorem toConeFromOverX_eq (f : X ⟶ B) (g : Y ⟶ B) :
    toConeFromOverX f g =
      DerivedCategory.Q.map
        (toMappingConeCochain (pullback.fst f g) f ≫ fromOverXCochain f g) :=
  sorry

/-- The diagram arrow `L_{W/Y} ⟶ E`, as `DerivedCategory.Q.map` of
`toMappingConeCochain` composed with `fromOverYCochain`. -/
def toConeFromOverY (f : X ⟶ B) (g : Y ⟶ B) :
    cotangent (pullback.snd f g) ⟶ cone f g :=
  DerivedCategory.Q.map
    (toMappingConeCochain (pullback.snd f g) g ≫ fromOverYCochain f g)

/-- Unfolding of `toConeFromOverY` as `DerivedCategory.Q.map` of the composite
`toMappingConeCochain ≫ fromOverYCochain`. -/
theorem toConeFromOverY_eq (f : X ⟶ B) (g : Y ⟶ B) :
    toConeFromOverY f g =
      DerivedCategory.Q.map
        (toMappingConeCochain (pullback.snd f g) g ≫ fromOverYCochain f g) :=
  sorry

/-- The connecting map `E ⟶ (Lp^* L_{X/B})⟦1⟧` of the top row, induced by
`mappingCone.triangle.mor₃` of `sumMapCochain` and projection to the first summand. -/
def topConnectingMap (f : X ⟶ B) (g : Y ⟶ B) :
    cone f g ⟶ (pullbackCotangent (pullback.fst f g) f)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map
      ((mappingCone.triangle (sumMapCochain f g)).mor₃ ≫ biprod.fst⟦(1 : ℤ)⟧') ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
      (pullbackCotangentCochain (pullback.fst f g) f)

/-- Unfolding of `topConnectingMap` from `mappingCone.triangle.mor₃` and `biprod.fst`. -/
theorem topConnectingMap_eq (f : X ⟶ B) (g : Y ⟶ B) :
    topConnectingMap f g =
      DerivedCategory.Q.map
          ((mappingCone.triangle (sumMapCochain f g)).mor₃ ≫
            biprod.fst⟦(1 : ℤ)⟧') ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (pullbackCotangentCochain (pullback.fst f g) f) :=
  sorry

/-- The connecting map `E ⟶ (Lq^* L_{Y/B})⟦1⟧` of the right column, induced by
`mappingCone.triangle.mor₃` of `sumMapCochain` and projection to the second summand. -/
def rightConnectingMap (f : X ⟶ B) (g : Y ⟶ B) :
    cone f g ⟶ (pullbackCotangent (pullback.snd f g) g)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map
      ((mappingCone.triangle (sumMapCochain f g)).mor₃ ≫ biprod.snd⟦(1 : ℤ)⟧') ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
      (pullbackCotangentCochain (pullback.snd f g) g)

/-- Unfolding of `rightConnectingMap` from `mappingCone.triangle.mor₃` and `biprod.snd`. -/
theorem rightConnectingMap_eq (f : X ⟶ B) (g : Y ⟶ B) :
    rightConnectingMap f g =
      DerivedCategory.Q.map
          ((mappingCone.triangle (sumMapCochain f g)).mor₃ ≫
            biprod.snd⟦(1 : ℤ)⟧') ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (pullbackCotangentCochain (pullback.snd f g) g) :=
  sorry

/-- The top row `Lp^* L_{X/B} ⟶ L_{W/Y} ⟶ E ⟶ (Lp^* L_{X/B})⟦1⟧` of the fibre-product
diagram. -/
def topTriangle (f : X ⟶ B) (g : Y ⟶ B) :
    Triangle (DerivedCategory (CommModules (pullback f g))) :=
  Triangle.mk (topMap f g) (toConeFromOverY f g) (topConnectingMap f g)

/-- The right column `Lq^* L_{Y/B} ⟶ L_{W/X} ⟶ E ⟶ (Lq^* L_{Y/B})⟦1⟧` of the
fibre-product diagram. -/
def rightTriangle (f : X ⟶ B) (g : Y ⟶ B) :
    Triangle (DerivedCategory (CommModules (pullback f g))) :=
  Triangle.mk (rightMap f g) (toConeFromOverX f g) (rightConnectingMap f g)

/-- The mapping-cone triangle of `sumMapCochain` is distinguished in `D(𝒪_W)`. -/
theorem cone_triangle_distinguished (f : X ⟶ B) (g : Y ⟶ B) :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (sumMapCochain f g)) ∈
      distTriang (DerivedCategory (CommModules (pullback f g))) :=
  sorry

/-- The middle row of the fibre-product diagram is the transitivity triangle of
`W ⟶ X ⟶ B`. -/
theorem middleRow (f : X ⟶ B) (g : Y ⟶ B) :
    transitivityTriangle (pullback.fst f g) f =
      Triangle.mk (transitivityMap (pullback.fst f g) f)
        (toRelativeMap (pullback.fst f g) f)
        (connectingMap (pullback.fst f g) f) :=
  sorry

/-- The middle column of the fibre-product diagram is the transitivity triangle of
`W ⟶ Y ⟶ B`. -/
theorem middleColumn (f : X ⟶ B) (g : Y ⟶ B) :
    transitivityTriangle (pullback.snd f g) g =
      Triangle.mk (transitivityMap (pullback.snd f g) g)
        (toRelativeMap (pullback.snd f g) g)
        (connectingMap (pullback.snd f g) g) :=
  sorry

/-- The top row of the fibre-product diagram is distinguished in `D(𝒪_W)`. -/
theorem topTriangle_distinguished (f : X ⟶ B) (g : Y ⟶ B) :
    topTriangle f g ∈ distTriang (DerivedCategory (CommModules (pullback f g))) :=
  sorry

/-- The right column of the fibre-product diagram is distinguished in `D(𝒪_W)`. -/
theorem rightTriangle_distinguished (f : X ⟶ B) (g : Y ⟶ B) :
    rightTriangle f g ∈ distTriang (DerivedCategory (CommModules (pullback f g))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct
