/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.ULift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Algebraic-space representations of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver BasedFunctor BasedNatIso
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme.Classifying

variable {S : Scheme.{u}}

/-- The universe-lifted slice projection of a scheme over `S`. -/
def sliceProjection (U : Over S) : ULiftHom.{u + 1} (Over U) ⥤ Over S :=
  (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙ Over.forget U

/-- The universe-lifted slice projection is fibred in groupoids. -/
instance sliceProjection.instIsFiberedInGroupoids (U : Over S) :
    Functor.IsFibered.InGroupoids (sliceProjection U) := sorry

/-- The canonical slice of a scheme over `S` in the bicategory with Hom-universe `u + 1`. -/
def slice (U : Over S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (sliceProjection U)

/-- The projection of `slice U` is the universe-lifted slice projection. -/
theorem slice_p (U : Over S) : (slice U).p = sliceProjection U := sorry

/-- The universe-lifted category-of-elements projection of an algebraic space. -/
def toGroupoidsProjection (F : AlgebraicSpace S) :
    ULiftHom.{u + 1} F.functorOfPoints.Elementsᵒᵖ ⥤ Over S :=
  (ULiftHom.down : ULiftHom.{u + 1} F.functorOfPoints.Elementsᵒᵖ ⥤
      F.functorOfPoints.Elementsᵒᵖ) ⋙
    (CategoryOfElements.π F.functorOfPoints).leftOp

/-- The universe-lifted category-of-elements projection is fibred in groupoids. -/
instance toGroupoidsProjection.instIsFiberedInGroupoids (F : AlgebraicSpace S) :
    Functor.IsFibered.InGroupoids (toGroupoidsProjection F) := sorry

/-- The groupoid fibration of an algebraic space in the bicategory with Hom-universe `u + 1`. -/
def toGroupoids (F : AlgebraicSpace S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (toGroupoidsProjection F)

/-- The projection of `toGroupoids F` is the universe-lifted category-of-elements
projection. -/
theorem toGroupoids_p (F : AlgebraicSpace S) :
    (toGroupoids F).p = toGroupoidsProjection F := sorry

/-- A morphism of algebraic spaces induces a 1-morphism of the associated
groupoid fibrations. -/
def toGroupoids.map {F G : AlgebraicSpace S} (f : F ⟶ G) :
    toGroupoids F ⟶ toGroupoids G :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor :=
        (ULiftHom.down : ULiftHom.{u + 1} F.functorOfPoints.Elementsᵒᵖ ⥤
            F.functorOfPoints.Elementsᵒᵖ) ⋙
          (CategoryOfElements.map f).op ⋙
          (ULiftHom.up : G.functorOfPoints.Elementsᵒᵖ ⥤
            ULiftHom.{u + 1} G.functorOfPoints.Elementsᵒᵖ)
      w := sorry }

/-- `toGroupoids.map` sends identity morphisms of algebraic spaces to identity
1-morphisms. -/
theorem toGroupoids.map_id (F : AlgebraicSpace S) :
    toGroupoids.map (𝟙 F) = 𝟙 (toGroupoids F) := sorry

/-- The groupoid fibration of a scheme over `S` is canonically equivalent to the
universe-lifted slice fibration. -/
def ofOverSliceEquiv (U : Over S) :
    toGroupoids (AlgebraicSpace.ofOver U) ≌ slice U :=
  let homBF :
      BasedFunctor
        (toGroupoids (AlgebraicSpace.ofOver U)).toBasedCategory
        (slice U).toBasedCategory :=
    { obj := fun x : ULiftHom.{u + 1, u + 1}
          (AlgebraicSpace.ofOver U).functorOfPoints.Elementsᵒᵖ ↦
        (ULiftHom.objUp.{u + 1, u + 1}
          (Over.mk (ULiftHom.objDown.{u + 1, u + 1} x).unop.2) :
          ULiftHom.{u + 1, u + 1} (Over U))
      map := fun f ↦ ⟨Over.homMk f.down.unop.1.unop sorry⟩
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let invBF :
      BasedFunctor
        (slice U).toBasedCategory
        (toGroupoids (AlgebraicSpace.ofOver U)).toBasedCategory :=
    { obj := fun α : ULiftHom.{u + 1, u + 1} (Over U) ↦
        (ULiftHom.objUp.{u + 1, u + 1}
          (Opposite.op ⟨Opposite.op α.objDown.left, α.objDown.hom⟩) :
          ULiftHom.{u + 1, u + 1} (AlgebraicSpace.ofOver U).functorOfPoints.Elementsᵒᵖ)
      map := fun {α β} (κ : α ⟶ β) ↦
        let α' : Over U := ULiftHom.objDown.{u + 1, u + 1} α
        let β' : Over U := ULiftHom.objDown.{u + 1, u + 1} β
        ⟨Quiver.Hom.op
          (CategoryOfElements.homMk
            (⟨Opposite.op β'.left, β'.hom⟩ :
              (AlgebraicSpace.ofOver U).functorOfPoints.Elements)
            (⟨Opposite.op α'.left, α'.hom⟩ :
              (AlgebraicSpace.ofOver U).functorOfPoints.Elements)
            κ.down.left.op sorry)⟩
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let qi : BasedFunctor.QuasiInverse homBF :=
    { inverse := invBF
      unitIso := BasedNatIso.ofComponents (fun x ↦ Iso.refl _) sorry sorry
      counitIso := BasedNatIso.ofComponents (fun α ↦ Iso.refl _) sorry sorry }
  Bicategory.InducedBicategory.equivalenceMk qi.toEquivalence

/-- The unit of `ofOverSliceEquiv` identifies the composite of the comparison with
its inverse. -/
theorem ofOverSliceEquiv_hom (U : Over S) :
    Nonempty
      ((ofOverSliceEquiv U).hom ≫ (ofOverSliceEquiv U).inv ≅
        𝟙 (toGroupoids (AlgebraicSpace.ofOver U))) := sorry

/-- A slice 2-fibre product of `f` along `y : slice U ⟶ Y` is represented by an
algebraic space `Fy` over `S` with structure morphism `fy : Fy ⟶ ofOver U`
when the apex is equivalent to `toGroupoids Fy` and the projection triangle
identifies `toGroupoids.map fy` with `TwoFibreProduct.fst` along
`ofOverSliceEquiv`. -/
def RepresentsBaseChange
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) {U : Over S} (y : slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ AlgebraicSpace.ofOver U) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} y f ≌ toGroupoids Fy,
    Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u + 1} y f)

/-- A representing algebraic space is equivalent to the slice 2-fibre product. -/
theorem RepresentsBaseChange.apex_equivalence
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {f : X ⟶ Y} {U : Over S} {y : slice U ⟶ Y} {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    Nonempty
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} y f ≌ toGroupoids Fy) :=
  sorry

/-- The structure morphism of a representing algebraic space recovers the
projection of the slice 2-fibre product along `ofOverSliceEquiv`. -/
theorem RepresentsBaseChange.projection_triangle
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {f : X ⟶ Y} {U : Over S} {y : slice U ⟶ Y} {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u + 1} y f ≌ toGroupoids Fy,
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u + 1} y f) :=
  sorry

/-- A 1-morphism in the lifted bicategory of groupoid fibrations is representable by
algebraic spaces when every slice base change is represented by an algebraic
space over `S`. -/
def relativelyRepresentableByAlgebraicSpaces :
    MorphismProperty
      (FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :=
  fun _ Y f ↦ ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y),
    ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange f y Fy fy

/-- Relative representability by algebraic spaces means every slice base change
is represented by an algebraic space over `S`. -/
theorem relativelyRepresentableByAlgebraicSpaces.iff
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y),
        ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          RepresentsBaseChange f y Fy fy := sorry

/-- A 1-morphism in the lifted bicategory of groupoid fibrations is smooth when it is
representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is a smooth morphism of algebraic spaces. -/
class Smooth
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is smooth. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Smooth fy

/-- A 1-morphism in the lifted bicategory of groupoid fibrations is surjective when it is
representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is a surjective morphism of algebraic spaces. -/
class Surjective
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is surjective. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Surjective fy

namespace Smooth

/-- The identity 1-morphism is smooth. -/
instance id
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Smooth (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a smooth 1-morphism is
smooth. -/
theorem spec
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Smooth f] {U : Over S} (y : slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) : AlgebraicSpace.Smooth fy := sorry

/-- A smooth 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Smooth f] : relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- Smoothness is representability by algebraic spaces together with smoothness
of every representing morphism. -/
theorem iff
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Smooth f ↔
      relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          RepresentsBaseChange f y Fy fy → AlgebraicSpace.Smooth fy := sorry

end Smooth

namespace Surjective

/-- The identity 1-morphism is surjective. -/
instance id
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Surjective (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a surjective 1-morphism is
surjective. -/
theorem spec
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Surjective f] {U : Over S} (y : slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) : AlgebraicSpace.Surjective fy :=
  sorry

/-- A surjective 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Surjective f] : relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- Surjectivity is representability by algebraic spaces together with
surjectivity of every representing morphism. -/
theorem iff
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Surjective f ↔
      relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          RepresentsBaseChange f y Fy fy → AlgebraicSpace.Surjective fy :=
  sorry

end Surjective

/-- The universe-lifted slice-change functor induced by a morphism in `Over S`. -/
def overMapFunctor {U V : Over S} (h : U ⟶ V) :
    ULiftHom.{u + 1} (Over U) ⥤ ULiftHom.{u + 1} (Over V) :=
  (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙
    Over.map h ⋙
    (ULiftHom.up : Over V ⥤ ULiftHom.{u + 1} (Over V))

/-- `overMapFunctor` lies strictly over `Over S`. -/
theorem overMapFunctor_p {U V : Over S} (h : U ⟶ V) :
    overMapFunctor h ⋙ sliceProjection V = sliceProjection U :=
  sorry

/-- The canonical 1-morphism `slice U ⟶ slice V` induced by `h : U ⟶ V`. -/
def overMap {U V : Over S} (h : U ⟶ V) : slice U ⟶ slice V :=
  Groupoids.ofBasedFunctor (BasedFunctor.ofFunctor (overMapFunctor h) (overMapFunctor_p h))

/-- The total functor of `overMap h` is `overMapFunctor h`. -/
theorem overMap_toFunctor {U V : Over S} (h : U ⟶ V) :
    FiberedCategoryOver.Groupoids.toFunctor (overMap h) = overMapFunctor h :=
  sorry

/-- The slice morphism induced by an identity is the identity. -/
theorem overMap_id (U : Over S) : overMap (𝟙 U) = 𝟙 (slice U) :=
  sorry

/-- The 1-morphism of slices induced by a morphism of schemes compatible with
the given structure morphisms over `S`. -/
def sliceHomMk {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    slice (Over.mk σK) ⟶ slice (Over.mk σL) :=
  overMap (Over.homMk g hg)

/-- `sliceHomMk g hg` is `overMap` of the corresponding morphism in `Over S`. -/
theorem sliceHomMk_eq {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    sliceHomMk g hg = overMap (Over.homMk g hg) :=
  sorry


end AlgebraicGeometry.GroupScheme.Classifying
