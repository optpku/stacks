/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity
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
  rfl

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
  rfl

/-- The cochain-level object `E` filling the upper-right corner of the fibre-product
diagram. -/
def coneCochain (f : X ⟶ B) (g : Y ⟶ B) : CochainComplex (CommModules (pullback f g)) ℤ :=
  mappingCone (sumMapCochain f g)

/-- Unfolding of `coneCochain` as a mapping cone. -/
theorem coneCochain_eq (f : X ⟶ B) (g : Y ⟶ B) :
    coneCochain f g = mappingCone (sumMapCochain f g) :=
  rfl

/-- The object `E` of `D(𝒪_{X ×_B Y})` filling the upper-right corner of the fibre-product
diagram of cotangent complexes. -/
def cone (f : X ⟶ B) (g : Y ⟶ B) : DerivedCategory (CommModules (pullback f g)) :=
  DerivedCategory.Q.obj (coneCochain f g)

/-- Unfolding of `cone` as `DerivedCategory.Q` of the mapping cone of `sumMapCochain`. -/
theorem cone_eq (f : X ⟶ B) (g : Y ⟶ B) :
    cone f g = DerivedCategory.Q.obj (coneCochain f g) :=
  rfl

/-- The canonical map `L_{W/B} ⟶ E` induced by `mappingCone.inr`. -/
def coneInr (f : X ⟶ B) (g : Y ⟶ B) :
    cotangent (toBase f g) ⟶ cone f g :=
  DerivedCategory.Q.map (mappingCone.inr (sumMapCochain f g))

/-- Unfolding of `coneInr` as `DerivedCategory.Q.map` of `mappingCone.inr`. -/
theorem coneInr_eq (f : X ⟶ B) (g : Y ⟶ B) :
    coneInr f g = DerivedCategory.Q.map (mappingCone.inr (sumMapCochain f g)) :=
  rfl

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
  rfl

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
  rfl

/-- The mapping-cone triangle of `sumMapCochain` is distinguished in `D(𝒪_W)`. -/
theorem cone_triangle_distinguished (f : X ⟶ B) (g : Y ⟶ B) :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (sumMapCochain f g)) ∈
      distTriang (DerivedCategory (CommModules (pullback f g))) :=
  sorry

/-- The two transitivity triangles on a fibre product admit compatible completions
with the cone of the sum of their first maps, making the outer row and column
distinguished triangles. -/
theorem diagram (f : X ⟶ B) (g : Y ⟶ B) :
    let p := pullback.fst f g
    let q := pullback.snd f g
    let t := DerivedCategory.Q.map (cotangentToBaseIso f g).inv
    ∃ (a : cotangent q ⟶ cone f g) (b : cotangent p ⟶ cone f g)
      (dp : cotangent p ⟶ (pullbackCotangent p f)⟦(1 : ℤ)⟧)
      (dq : cotangent q ⟶ (pullbackCotangent q g)⟦(1 : ℤ)⟧)
      (dt : cone f g ⟶ (pullbackCotangent p f)⟦(1 : ℤ)⟧)
      (dr : cone f g ⟶ (pullbackCotangent q g)⟦(1 : ℤ)⟧),
      Triangle.mk (transitivityMap p f) (toRelativeMap p f) dp ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (transitivityMap q g ≫ DerivedCategory.Q.map (cotangentToBaseIso f g).hom)
        (t ≫ toRelativeMap q g) dq ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (topMap f g) a dt ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (rightMap f g) b dr ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      t ≫ toRelativeMap q g ≫ a = coneInr f g ∧
      toRelativeMap p f ≫ b = coneInr f g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct
