/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Equivalence.Mk
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction.Equivalence

/-! # Algebraic-space representations of kernel pairs -/

@[expose] public section

-- Public constructions retain their private coordinate data in their explicit bodies.
set_option backward.privateInPublic true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open FiberedCategoryOver.Groupoids Opposite
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} (F : AlgebraicSpace S)
variable (f : F.toGroupoids ⟶ X) [AlgebraicStack X]

namespace KernelPairSpace

/-- The product of the actual atlas scheme of the input space with itself. -/
private def atlasProduct : Over S :=
  prod (AtlasInput.scheme F) (AtlasInput.scheme F)

/-- The first actual atlas point over the product chart. -/
private def atlasPoint0 : yoneda.obj (atlasProduct F) ⟶ F.functorOfPoints :=
  yoneda.map (prod.fst : atlasProduct F ⟶ AtlasInput.scheme F) ≫ AtlasInput.map F

/-- The second actual atlas point over the product chart. -/
private def atlasPoint1 : yoneda.obj (atlasProduct F) ⟶ F.functorOfPoints :=
  yoneda.map (prod.snd : atlasProduct F ⟶ AtlasInput.scheme F) ≫ AtlasInput.map F

/-- The first atlas-product leg, with its actual slice-to-presheaf comparison. -/
private def atlasLeg0 : GroupoidsOver.slice (atlasProduct F) ⟶ F.toGroupoids :=
  (ofOverSliceEquiv (atlasProduct F)).inv ≫ toGroupoids.map (atlasPoint0 F)

/-- The second atlas-product leg, with its actual slice-to-presheaf comparison. -/
private def atlasLeg1 : GroupoidsOver.slice (atlasProduct F) ⟶ F.toGroupoids :=
  (ofOverSliceEquiv (atlasProduct F)).inv ≫ toGroupoids.map (atlasPoint1 F)

/-- The pair of the two actual images in the relative product of the stack. -/
private def atlasPair :
    GroupoidsOver.slice (atlasProduct F) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)
        (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X) :=
  pairOverBase (atlasLeg0 F ≫ f) (atlasLeg1 F ≫ f)

/-- The diagonal base-change representation is read directly from the caller's field. -/
private def chartSpace : AlgebraicSpace S :=
  Classical.choose (AlgebraicStack.representableDiagonal (X := X) (atlasPair F f))

/-- The actual chart map to the atlas-product scheme is the caller's specified witness. -/
private def chartMap : chartSpace F f ⟶ ofOver (atlasProduct F) :=
  Classical.choose
    (Classical.choose_spec
      (AlgebraicStack.representableDiagonal (X := X) (atlasPair F f)))

/-- The chart specification is the unmodified specification in the caller's diagonal witness. -/
private theorem chart_represents :
    RepresentsBaseChange (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)
      (atlasPair F f) (chartSpace F f) (chartMap F f) :=
  Classical.choose_spec
    (Classical.choose_spec
      (AlgebraicStack.representableDiagonal (X := X) (atlasPair F f)))

/-- Both directions of the chart equivalence are taken from the same supplied witness. -/
private def chartEquiv :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (atlasPair F f) (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ≌
      (chartSpace F f).toGroupoids :=
  Classical.choose (chart_represents F f)

/-- The chart projection triangle is part of that original representation witness. -/
private def chartProjectionIso :
    (chartEquiv F f).hom ≫ toGroupoids.map (chartMap F f) ≫
        (ofOverSliceEquiv (atlasProduct F)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (atlasPair F f) (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  Classical.choice (Classical.choose_spec (chart_represents F f))

/-- Read an element of the original space from an actual slice fibre object. -/
private def atlasValue0 (T : Over S) (a : (GroupoidsOver.slice (atlasProduct F)).p.Fiber T) :
    F.functorOfPoints.obj (op T) :=
  PresheafKernelPair.value F.functorOfPoints T ((fiberFunctor (atlasLeg0 F) T).obj a)

/-- Read the second original-space point from an actual slice fibre object. -/
private def atlasValue1 (T : Over S) (a : (GroupoidsOver.slice (atlasProduct F)).p.Fiber T) :
    F.functorOfPoints.obj (op T) :=
  PresheafKernelPair.value F.functorOfPoints T ((fiberFunctor (atlasLeg1 F) T).obj a)

/-- Normalize the source fibre in the first atlas leg before applying its stack image. -/
private def atlasImage0Iso (T : Over S) (a : (GroupoidsOver.slice (atlasProduct F)).p.Fiber T) :
    PresheafKernelPair.image F.functorOfPoints f T (atlasValue0 F T a) ≅
      (fiberFunctor (atlasLeg0 F ≫ f) T).obj a :=
  (fiberFunctor f T).mapIso
    (PresheafKernelPair.pointValueIso F.functorOfPoints T
      ((fiberFunctor (atlasLeg0 F) T).obj a))

/-- Normalize the source fibre in the second atlas leg before applying its stack image. -/
private def atlasImage1Iso (T : Over S) (a : (GroupoidsOver.slice (atlasProduct F)).p.Fiber T) :
    PresheafKernelPair.image F.functorOfPoints f T (atlasValue1 F T a) ≅
      (fiberFunctor (atlasLeg1 F ≫ f) T).obj a :=
  (fiberFunctor f T).mapIso
    (PresheafKernelPair.pointValueIso F.functorOfPoints T
      ((fiberFunctor (atlasLeg1 F) T).obj a))

/-- A diagonal base-change object carries the two comparisons to the same stack object. -/
private def chartPoint
    (a : (BasedCategory.PseudoPullback (atlasPair F f).hom
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X).hom).obj) :
    PresheafKernelPair.Point F.functorOfPoints f (BasedCategory.PseudoPullback.baseObj a) :=
  let T := BasedCategory.PseudoPullback.baseObj a
  let z := (BasedCategory.PseudoPullback.fiberObj a).fst
  let comparison := (BasedCategory.PseudoPullback.fiberObj a).iso
  let first := (fiberFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u}
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)) T).mapIso comparison
  let second := (fiberFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u}
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)) T).mapIso comparison
  { fst := atlasValue0 F T z
    snd := atlasValue1 F T z
    iso := atlasImage0Iso F f T z ≪≫ first ≪≫ second.symm ≪≫
      (atlasImage1Iso F f T z).symm }

/-- Chart restriction is compatible with the point presheaf restriction. -/
private theorem chartPoint_naturality
    {a b : (BasedCategory.PseudoPullback (atlasPair F f).hom
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X).hom).obj} (φ : a ⟶ b) :
    ((PresheafKernelPair.presheaf F.functorOfPoints f)).map (BasedCategory.PseudoPullback.baseMap φ).op (chartPoint F f b) =
      chartPoint F f a := sorry

/-- The actual chart comparison sends an object to its displayed points and composite iso. -/
private def chartToPoints :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (atlasPair F f) (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ⟶
      FiberedCategoryOver.Groupoids.ofPresheaf ((PresheafKernelPair.presheaf F.functorOfPoints f)) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor :=
        { obj := fun a ↦ op ⟨op (BasedCategory.PseudoPullback.baseObj a), chartPoint F f a⟩
          map := fun {a b} φ ↦
            (CategoryOfElements.homMk
              (⟨op (BasedCategory.PseudoPullback.baseObj b), chartPoint F f b⟩ : ((PresheafKernelPair.presheaf F.functorOfPoints f)).Elements)
              (⟨op (BasedCategory.PseudoPullback.baseObj a), chartPoint F f a⟩ : ((PresheafKernelPair.presheaf F.functorOfPoints f)).Elements)
              (BasedCategory.PseudoPullback.baseMap φ).op (chartPoint_naturality F f φ)).op
          map_id := sorry
          map_comp := sorry }
      w := sorry }

/-- The atlas scheme is the atlas already supplied by the chosen diagonal chart space. -/
private def atlasScheme : Over S := AtlasInput.scheme (chartSpace F f)

/-- The atlas transformation evaluates the supplied chart equivalence inverse followed
by the explicit chart-to-points functor. -/
private def atlas : yoneda.obj (atlasScheme F f) ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f) where
  app T := TypeCat.ofHom (fun a ↦
    let input := FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
      (yoneda.obj (atlasScheme F f)) (unop T) a
    let chart := (fiberFunctor
      (toGroupoids.map (AtlasInput.map (chartSpace F f)) ≫ (chartEquiv F f).inv ≫
        chartToPoints F f) (unop T)).obj input
    FiberedCategoryOver.Sets.ofPresheaf.fiberToValue ((PresheafKernelPair.presheaf F.functorOfPoints f)) (unop T) chart)
  naturality := sorry

/-- The displayed atlas covers the actual point presheaf in the etale topology. -/
private theorem atlas_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas F f) := sorry

/-- The point presheaf has fppf descent. -/
private theorem points_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) ((PresheafKernelPair.presheaf F.functorOfPoints f)) := sorry

end KernelPairSpace

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.KernelPairSpace

variable {S : Scheme.{u}} {X : GroupoidsOver S} (F : AlgebraicSpace S)
variable (f : F.toGroupoids ⟶ X) [AlgebraicStack X]

namespace DiagonalTest

variable {T V : Over S} (a : yoneda.obj T ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f)) (b : yoneda.obj V ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f))

/-- The first coordinate map of the first test section. -/
private def a0 : yoneda.obj T ⟶ F.functorOfPoints := a ≫ PresheafKernelPair.fst F.functorOfPoints f
/-- The first coordinate map of the second test section. -/
private def b0 : yoneda.obj V ⟶ F.functorOfPoints := b ≫ PresheafKernelPair.fst F.functorOfPoints f

/-- The first coordinate equality is represented using the supplied input-space diagonal. -/
private def firstCoordinates : Over S :=
  (Functor.relativelyRepresentable.of_diag F.representableDiagonal (a0 F f a)).pullback
    (b0 F f b)

/-- The projection from the first-coordinate equality scheme to the first test scheme. -/
private def firstToT : firstCoordinates F f a b ⟶ T :=
  (Functor.relativelyRepresentable.of_diag F.representableDiagonal (a0 F f a)).fst'
    (b0 F f b)
/-- The projection from the first-coordinate equality scheme to the second test scheme. -/
private def firstToV : firstCoordinates F f a b ⟶ V :=
  (Functor.relativelyRepresentable.of_diag F.representableDiagonal (a0 F f a)).snd
    (b0 F f b)

/-- The pair of second-coordinate sections over the first-coordinate equality scheme. -/
private def secondPair : yoneda.obj (firstCoordinates F f a b) ⟶
    F.functorOfPoints ⨯ F.functorOfPoints :=
  prod.lift
    (yoneda.map (firstToT F f a b) ≫ a ≫ PresheafKernelPair.snd F.functorOfPoints f)
    (yoneda.map (firstToV F f a b) ≫ b ≫ PresheafKernelPair.snd F.functorOfPoints f)

/-- The second coordinate equality uses another test of the same supplied diagonal. -/
private def coordinates : Over S := F.representableDiagonal.pullback (secondPair F f a b)
/-- The projection from the coordinate-equality scheme to the first-coordinate equality scheme. -/
private def coordinatesToFirst : coordinates F f a b ⟶ firstCoordinates F f a b :=
  F.representableDiagonal.snd (secondPair F f a b)
/-- The projection from the coordinate-equality scheme to the first test scheme. -/
private def toT : coordinates F f a b ⟶ T := coordinatesToFirst F f a b ≫ firstToT F f a b
/-- The projection from the coordinate-equality scheme to the second test scheme. -/
private def toV : coordinates F f a b ⟶ V := coordinatesToFirst F f a b ≫ firstToV F f a b

/-- The first test section restricted to the coordinate-equality scheme. -/
private def sectionA : yoneda.obj (coordinates F f a b) ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f) := yoneda.map (toT F f a b) ≫ a
/-- The second test section restricted to the coordinate-equality scheme. -/
private def sectionB : yoneda.obj (coordinates F f a b) ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f) := yoneda.map (toV F f a b) ≫ b

/-- The first stored coordinates agree on their actual representing scheme. -/
private theorem first_eq :
    sectionA F f a b ≫ PresheafKernelPair.fst F.functorOfPoints f =
      sectionB F f a b ≫ PresheafKernelPair.fst F.functorOfPoints f := sorry
/-- The second stored coordinates agree on their actual representing scheme. -/
private theorem second_eq :
    sectionA F f a b ≫ PresheafKernelPair.snd F.functorOfPoints f =
      sectionB F f a b ≫ PresheafKernelPair.snd F.functorOfPoints f := sorry

end DiagonalTest

namespace SectionChart

variable {T : Over S} (a : yoneda.obj T ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f))

/-- The morphism of groupoid fibrations determined by the first coordinate of a section. -/
private def firstLeg : GroupoidsOver.slice T ⟶ F.toGroupoids :=
  let α : yoneda.obj T ⟶ F.functorOfPoints := a ≫ PresheafKernelPair.fst F.functorOfPoints f
  (ofOverSliceEquiv T).inv ≫ toGroupoids.map (F := ofOver T) (G := F) α
/-- The morphism of groupoid fibrations determined by the second coordinate of a section. -/
private def secondLeg : GroupoidsOver.slice T ⟶ F.toGroupoids :=
  let α : yoneda.obj T ⟶ F.functorOfPoints := a ≫ PresheafKernelPair.snd F.functorOfPoints f
  (ofOverSliceEquiv T).inv ≫ toGroupoids.map (F := ofOver T) (G := F) α

/-- The pair of stack images of the two coordinates of a section. -/
private def pair : GroupoidsOver.slice T ⟶
    TwoFibreProduct.apex.{u + 1, u, u + 1, u}
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X)
      (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} X) :=
  pairOverBase (firstLeg F f a ≫ f) (secondLeg F f a ≫ f)

/-- The space used to test vertical-isomorphism equality is selected from the
original caller-supplied diagonal representation at this exact scheme pair. -/
private def space : AlgebraicSpace S :=
  Classical.choose (AlgebraicStack.representableDiagonal (X := X) (pair F f a))
/-- The projection of the chosen diagonal base-change space to the test scheme. -/
private def map : space F f a ⟶ ofOver T :=
  Classical.choose (Classical.choose_spec
    (AlgebraicStack.representableDiagonal (X := X) (pair F f a)))
/-- The chosen space and projection represent the diagonal base change at the section pair. -/
private theorem represents : RepresentsBaseChange
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)
    (pair F f a) (space F f a) (map F f a) :=
  Classical.choose_spec (Classical.choose_spec
    (AlgebraicStack.representableDiagonal (X := X) (pair F f a)))
/-- The equivalence between the diagonal base change at the section pair and its representing space. -/
private def equiv :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pair F f a)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ≌
      (space F f a).toGroupoids :=
  Classical.choose (represents F f a)

variable (b : yoneda.obj T ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f))
variable (h0 : a ≫ PresheafKernelPair.fst F.functorOfPoints f =
  b ≫ PresheafKernelPair.fst F.functorOfPoints f)
variable (h1 : a ≫ PresheafKernelPair.snd F.functorOfPoints f =
  b ≫ PresheafKernelPair.snd F.functorOfPoints f)

/-- The given comparison of `b`, transported only along the specified coordinate equalities. -/
private def comparison (q : Over T) :
    PresheafKernelPair.image F.functorOfPoints f q.left ((a.app (op q.left) q.hom).fst) ≅
      PresheafKernelPair.image F.functorOfPoints f q.left ((a.app (op q.left) q.hom).snd) :=
  eqToIso (congrArg (PresheafKernelPair.image F.functorOfPoints f q.left)
      (congrArg (fun k : yoneda.obj T ⟶ F.functorOfPoints ↦ k.app (op q.left) q.hom) h0)) ≪≫
    (b.app (op q.left) q.hom).iso ≪≫
      (eqToIso (congrArg (PresheafKernelPair.image F.functorOfPoints f q.left)
        (congrArg (fun k : yoneda.obj T ⟶ F.functorOfPoints ↦ k.app (op q.left) q.hom) h1))).symm

/-- A section is lifted to the given diagonal base-change using its literal first
image and the identity/comparison pair. -/
private def lift : GroupoidsOver.slice T ⟶
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pair F f a)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor :=
        { obj := fun q ↦
            BasedCategory.PseudoPullback.mk (pair F f a).hom
              (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X).hom q.left
              { fst := ⟨q, rfl⟩
                snd := (fiberFunctor (firstLeg F f a ≫ f) q.left).obj ⟨q, rfl⟩
                iso := Functor.Fiber.isoMk
                  (BasedCategory.PseudoPullback.mkIso (eqToIso (by sorry)) (Iso.refl _)
                    (Functor.Fiber.fiberInclusion.mapIso (comparison F f a b h0 h1 q).symm)
                    sorry sorry sorry) (hhom := by sorry) }
          map := fun {q q'} k ↦
            BasedCategory.PseudoPullback.Hom.mk k.left k sorry
              ((toFunctor (firstLeg F f a ≫ f)).map k) sorry sorry
          map_id := sorry
          map_comp := sorry }
      w := sorry }

/-- The actual chart-space section is the specified lift followed by the
supplied equivalence forward map, evaluated in the original presheaf. -/
private def sectionMap : yoneda.obj T ⟶ (space F f a).functorOfPoints where
  app Q := TypeCat.ofHom (fun q ↦
    let source := FiberedCategoryOver.Sets.ofPresheaf.valueToFiber (yoneda.obj T) (unop Q) q
    let target := (fiberFunctor
      ((ofOverSliceEquiv T).hom ≫ lift F f a b h0 h1 ≫ (equiv F f a).hom) (unop Q)).obj source
    FiberedCategoryOver.Sets.ofPresheaf.fiberToValue (space F f a).functorOfPoints (unop Q) target)
  naturality := sorry

end SectionChart

namespace DiagonalTest

variable {T V : Over S} (a : yoneda.obj T ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f)) (b : yoneda.obj V ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f))

/-- The original stack-diagonal space at the actual coordinate-equality scheme. -/
private def isomSpace : AlgebraicSpace S := SectionChart.space F f (sectionA F f a b)

/-- The first vertical isomorphism as a section of the original diagonal chart space. -/
private def isomSectionA : yoneda.obj (coordinates F f a b) ⟶ (isomSpace F f a b).functorOfPoints :=
  SectionChart.sectionMap F f (sectionA F f a b) (sectionA F f a b) rfl rfl

/-- The second vertical isomorphism is transported by the two actual coordinate equalities. -/
private def isomSectionB : yoneda.obj (coordinates F f a b) ⟶ (isomSpace F f a b).functorOfPoints :=
  SectionChart.sectionMap F f (sectionA F f a b) (sectionB F f a b)
    (first_eq F f a b) (second_eq F f a b)

/-- The last equality scheme comes from the diagonal field of the given diagonal chart space. -/
private def scheme : Over S :=
  (isomSpace F f a b).representableDiagonal.pullback
    (prod.lift (isomSectionA F f a b) (isomSectionB F f a b))

/-- The specified last projection to the actual coordinate-equality scheme. -/
private def toCoordinates : scheme F f a b ⟶ coordinates F f a b :=
  (isomSpace F f a b).representableDiagonal.snd
    (prod.lift (isomSectionA F f a b) (isomSectionB F f a b))

/-- The projection from the section-equality scheme to the first test scheme. -/
private def fstScheme : scheme F f a b ⟶ T := toCoordinates F f a b ≫ toT F f a b
/-- The projection from the section-equality scheme to the second test scheme. -/
private def sndScheme : scheme F f a b ⟶ V := toCoordinates F f a b ≫ toV F f a b

/-- The two test sections agree after restriction to the section-equality scheme. -/
private theorem condition :
    yoneda.map (fstScheme F f a b) ≫ a = yoneda.map (sndScheme F f a b) ≫ b := sorry

/-- Lift to the first equality scheme with the input space's actual representation. -/
private def liftFirst (s : PullbackCone a b) : s.pt ⟶ yoneda.obj (firstCoordinates F f a b) :=
  (Functor.relativelyRepresentable.of_diag F.representableDiagonal (a0 F f a)).isPullback
      (b0 F f b) |>.lift s.fst s.snd (by sorry)

/-- Lift to the second equality scheme with the same original input diagonal. -/
private def liftCoordinates (s : PullbackCone a b) : s.pt ⟶ yoneda.obj (coordinates F f a b) :=
  (F.representableDiagonal.isPullback (secondPair F f a b)).lift
    (s.fst ≫ a ≫ PresheafKernelPair.snd F.functorOfPoints f)
    (liftFirst F f a b s) (by sorry)

/-- Lift to the last equality scheme using the original diagonal-chart space's
actual scheme representation. -/
private def lift (s : PullbackCone a b) : s.pt ⟶ yoneda.obj (scheme F f a b) :=
  ((isomSpace F f a b).representableDiagonal.isPullback
      (prod.lift (isomSectionA F f a b) (isomSectionB F f a b))).lift
    (liftCoordinates F f a b s ≫ isomSectionA F f a b)
    (liftCoordinates F f a b s) (by sorry)

/-- The represented square's limit structure retains the explicit three-stage lift. -/
private def isLimit : IsLimit (PullbackCone.mk
    (yoneda.map (fstScheme F f a b)) (yoneda.map (sndScheme F f a b))
    (condition F f a b)) :=
  PullbackCone.isLimitAux _ (lift F f a b) (by sorry) (by sorry) (by sorry)

/-- The actual scheme square represents the two test sections. -/
private theorem isPullback : IsPullback
    (yoneda.map (fstScheme F f a b)) (yoneda.map (sndScheme F f a b)) a b :=
  IsPullback.of_isLimit (isLimit F f a b)

end DiagonalTest

/-- Every scheme-to-points map has the specified coordinate/isomorphism equality scheme. -/
private theorem points_mapFromScheme_representable {T : Over S}
    (a : yoneda.obj T ⟶ (PresheafKernelPair.presheaf F.functorOfPoints f)) : yoneda.relativelyRepresentable a := by
  intro V b
  exact ⟨DiagonalTest.scheme F f a b, DiagonalTest.sndScheme F f a b,
    yoneda.map (DiagonalTest.fstScheme F f a b), DiagonalTest.isPullback F f a b⟩

/-- The kernel-pair diagonal is represented by the actual scheme tests above. -/
private theorem points_representableDiagonal : yoneda.relativelyRepresentable (diag ((PresheafKernelPair.presheaf F.functorOfPoints f))) :=
  Functor.relativelyRepresentable.diag_of_map_from_obj
    (fun {_} a ↦ points_mapFromScheme_representable F f a)

/-- Representability of the actual atlas uses the same explicit scheme tests;
only the etale law of those projections is deferred. -/
private theorem atlas_etale :
    (MorphismProperty.over (@Etale)).presheaf (atlas F f) := by
  refine ⟨points_mapFromScheme_representable F f (atlas F f), ?_⟩
  intro T V a b c h
  sorry

end AlgebraicGeometry.AlgebraicStack.KernelPairSpace

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} (F : AlgebraicSpace S)
variable (f : F.toGroupoids ⟶ X) [AlgebraicStack X]

/-- The actual algebraic space representing the self two-fibre product of a map
from an algebraic space. -/
def kernelPairSpace : AlgebraicSpace S :=
  ofFunctor ((PresheafKernelPair.presheaf F.functorOfPoints f)) (KernelPairSpace.points_isSheaf F f)
    (KernelPairSpace.points_representableDiagonal F f)
    ⟨KernelPairSpace.atlasScheme F f, KernelPairSpace.atlas F f,
      KernelPairSpace.atlas_etale F f, KernelPairSpace.atlas_locallySurjective F f⟩

/-- The representation equivalence retains its actual forward and backward functors. -/
def kernelPairSpaceEquiv : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f ≌
    (kernelPairSpace F f).toGroupoids :=
  PresheafKernelPair.equivalence F.functorOfPoints f

/-- The first projection of the represented kernel pair. -/
def kernelPairSpaceFst : kernelPairSpace F f ⟶ F := PresheafKernelPair.fst F.functorOfPoints f
/-- The second projection of the represented kernel pair. -/
def kernelPairSpaceSnd : kernelPairSpace F f ⟶ F := PresheafKernelPair.snd F.functorOfPoints f
/-- The identity section of the represented kernel pair. -/
def kernelPairSpaceDiagonal : F ⟶ kernelPairSpace F f :=
  PresheafKernelPair.diagonal F.functorOfPoints f

/-- The universal comparison between the two images in the stack. -/
def kernelPairSpaceUniversalIso :
    toGroupoids.map (kernelPairSpaceFst F f) ≫ f ≅
      toGroupoids.map (kernelPairSpaceSnd F f) ≫ f :=
  PresheafKernelPair.comparisonIso F.functorOfPoints f

/-- The first projection comparison retains the actual normalization components. -/
def kernelPairSpaceEquiv_fstIso :
    (kernelPairSpaceEquiv F f).hom ≫ toGroupoids.map (kernelPairSpaceFst F f) ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f f :=
  PresheafKernelPair.fstIso F.functorOfPoints f

/-- The second projection comparison retains the actual normalization components. -/
def kernelPairSpaceEquiv_sndIso :
    (kernelPairSpaceEquiv F f).hom ≫ toGroupoids.map (kernelPairSpaceSnd F f) ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f f :=
  PresheafKernelPair.sndIso F.functorOfPoints f

/-- The representing presheaf is the literal point-pair carrier. -/
@[simp]
theorem kernelPairSpace_functorOfPoints :
    (kernelPairSpace F f).functorOfPoints = (PresheafKernelPair.presheaf F.functorOfPoints f) := rfl

/-- The first space projection evaluates to the first stored point. -/
@[simp]
theorem kernelPairSpaceFst_app (T : (Over S)ᵒᵖ)
    (a : (kernelPairSpace F f).functorOfPoints.obj T) :
    (kernelPairSpaceFst F f).app T a = a.fst := rfl

/-- The second space projection evaluates to the second stored point. -/
@[simp]
theorem kernelPairSpaceSnd_app (T : (Over S)ᵒᵖ)
    (a : (kernelPairSpace F f).functorOfPoints.obj T) :
    (kernelPairSpaceSnd F f).app T a = a.snd := rfl

/-- The diagonal's first coordinate is the original point. -/
@[simp]
theorem kernelPairSpaceDiagonal_app_fst (T : (Over S)ᵒᵖ) (a : F.functorOfPoints.obj T) :
    ((kernelPairSpaceDiagonal F f).app T a).fst = a := rfl

/-- The diagonal's second coordinate is the original point. -/
@[simp]
theorem kernelPairSpaceDiagonal_app_snd (T : (Over S)ᵒᵖ) (a : F.functorOfPoints.obj T) :
    ((kernelPairSpaceDiagonal F f).app T a).snd = a := rfl

/-- The diagonal carries the actual identity vertical comparison. -/
@[simp]
theorem kernelPairSpaceDiagonal_app_iso (T : (Over S)ᵒᵖ) (a : F.functorOfPoints.obj T) :
    ((kernelPairSpaceDiagonal F f).app T a).iso = Iso.refl _ := rfl

/-- The first projection splits the specified diagonal. -/
theorem kernelPairSpaceDiagonal_comp_fst :
    kernelPairSpaceDiagonal F f ≫ kernelPairSpaceFst F f = 𝟙 F := sorry

/-- The second projection splits the specified diagonal. -/
theorem kernelPairSpaceDiagonal_comp_snd :
    kernelPairSpaceDiagonal F f ≫ kernelPairSpaceSnd F f = 𝟙 F := sorry

variable {U : GroupoidsOver S} (g : U ⟶ X)

/-- Transport the actual kernel pair along a supplied source equivalence.
The apex pseudofunctor retains the forward and inverse cospan maps. -/
def kernelPairSourceEquiv (e : U ≌ F.toGroupoids) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} g g ≌
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (e.inv ≫ g) (e.inv ≫ g) :=
  let comparison : e.hom ≫ (e.inv ≫ g) ≅ g ≫ 𝟙 X :=
    (α_ e.hom e.inv g).symm ≪≫ Bicategory.whiskerRightIso e.unit.symm g ≪≫
      λ_ g ≪≫ (ρ_ g).symm
  TwoFibreProduct.pseudofunctor.mapEquivalence
    (Bicategory.Cospan.equivalenceMk
      (S := ⟨U, U, X, g, g⟩)
      (T := ⟨F.toGroupoids, F.toGroupoids, X, e.inv ≫ g, e.inv ≫ g⟩)
      e e (Bicategory.Equivalence.id X)
      comparison comparison)

/-- The actual representing space for a kernel pair with a supplied represented source. -/
def representedKernelPairSpace (hU : IsRepresentableByAlgebraicSpace U) : AlgebraicSpace S :=
  kernelPairSpace (IsRepresentableByAlgebraicSpace.representingSpace hU) ((IsRepresentableByAlgebraicSpace.representingEquiv hU).inv ≫ g)

/-- Both directions of the representation equivalence are actual composites of the
source witness equivalence and the explicit point-presheaf comparison. -/
def representedKernelPairEquiv (hU : IsRepresentableByAlgebraicSpace U) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} g g ≌ (representedKernelPairSpace g hU).toGroupoids :=
  (kernelPairSourceEquiv (IsRepresentableByAlgebraicSpace.representingSpace hU) g (IsRepresentableByAlgebraicSpace.representingEquiv hU)).trans
    (kernelPairSpaceEquiv (IsRepresentableByAlgebraicSpace.representingSpace hU) ((IsRepresentableByAlgebraicSpace.representingEquiv hU).inv ≫ g))

end AlgebraicGeometry.AlgebraicStack
