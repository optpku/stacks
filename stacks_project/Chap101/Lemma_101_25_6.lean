module

public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_7_4_Points
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Lifting valuation rings through flat morphisms of algebraic stacks

A flat morphism of algebraic stacks lifts a valuation-ring point of the target
after an extension of valuation rings, provided the closed point of the source
spectrum lands in the image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The morphism of algebraic stacks over `S` induced by a morphism of schemes
compatible with the given structure morphisms. -/
def sliceHomMk {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    GroupoidsOver.slice (Over.mk σK) ⟶ GroupoidsOver.slice (Over.mk σL) :=
  overMap (Over.homMk g hg)

/-- `sliceHomMk g hg` is `overMap` of the corresponding morphism in `Over S`. -/
theorem sliceHomMk_eq {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S}
    {σL : XL ⟶ S} (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    sliceHomMk g hg = overMap (Over.homMk g hg) :=
  sorry

/-- The closed point of `Spec(A)` as a point of the algebraic stack associated to
a morphism `Spec (.of A) ⟶ S`. -/
def specClosedPoint {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (.of A) ⟶ S) : Points (GroupoidsOver.slice (Over.mk σ)) :=
  Points.ofSlice (IsLocalRing.closedPoint A)

/-- `specClosedPoint σ` is the image of the closed point of `A` under
`Points.ofSlice`. -/
theorem specClosedPoint_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (σ : Spec (.of A) ⟶ S) :
    specClosedPoint σ = Points.ofSlice (IsLocalRing.closedPoint A) :=
  sorry

/-- The image of `specClosedPoint σ` along a morphism from the slice of
`Spec(A)` is `Points.mapSlice` of the closed point of `A`. -/
theorem specClosedPoint_map {S : Scheme.{u}} {Y : GroupoidsOver S}
    [AlgebraicStack Y] {A : Type u} [CommRing A] [IsLocalRing A]
    (σ : Spec (.of A) ⟶ S) (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y) :
    Points.map g (specClosedPoint σ) =
      Points.mapSlice g (IsLocalRing.closedPoint A) :=
  sorry

namespace Flat

/-- Lemma 101.25.6: Let `f : X ⟶ Y` be a flat morphism of algebraic stacks.
Let `Spec(A) ⟶ Y` be a morphism where `A` is a valuation ring. If the closed
point of `Spec(A)` maps to a point of `|Y|` in the image of `|X| ⟶ |Y|`, then
there exists a 2-commutative diagram `Spec(A') ⟶ X` over `Spec(A) ⟶ Y` where
`A → A'` is an extension of valuation rings in the sense of
`IsExtensionOfValuationRings` (More on Algebra, Definition 15.124.1). -/
@[stacks 0DN5]
theorem exists_isExtensionOfValuationRings {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} [Flat f] {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (σ : Spec (.of A) ⟶ S) (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (h_image : Points.map g (specClosedPoint σ) ∈ Set.range (Points.map f)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A')
      (_ : Algebra A A') (_ : IsExtensionOfValuationRings A A')
      (lift :
        GroupoidsOver.slice
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ σ)) ⟶
          X),
      Nonempty
        (sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap A A'))) rfl ≫ g ≅
          lift ≫ f) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
