/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

/-!
# Structure morphism of the stack of coherent sheaves

A finite-presentation morphism `f : X ⟶ B` of algebraic spaces determines a
1-morphism `forget f : toGroupoids f ⟶ Classifying.toGroupoids B` over
`Over S`, sending `(T, g, F)` to the functor-of-points element of `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme Opposite
open CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

section StructureFunctor

-- The exposed functor is assembled from private concrete map data and law proofs.
set_option backward.privateInPublic true

/-- A morphism of coherent sheaves respects the corresponding functor-of-points elements. -/
private theorem forgetMap_w (f : X ⟶ B) [FinitePresentation f] {x y : Obj f}
    (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (yonedaEquiv y.σ.hom) =
      yonedaEquiv x.σ.hom := by
  rw [yonedaEquiv_naturality]
  exact congrArg yonedaEquiv (CostructuredArrow.w α.base)

/-- The morphism on opposite elements induced by the base map of a coherent-sheaf morphism. -/
private def forgetMap (f : X ⟶ B) [FinitePresentation f] {x y : Obj f}
    (α : x ⟶ y) :
    ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) ⟶
      (ULiftHom.objUp (op ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩) :
        ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ) :=
  ⟨Quiver.Hom.op (CategoryOfElements.homMk
    ⟨op y.σ.left, yonedaEquiv y.σ.hom⟩ ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩
    α.base.left.op (forgetMap_w f α))⟩

/-- The map on opposite elements preserves identity morphisms. -/
private theorem forgetMap_id (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    forgetMap f (𝟙 x) = 𝟙 _ := rfl

/-- The map on opposite elements preserves composition. -/
private theorem forgetMap_comp (f : X ⟶ B) [FinitePresentation f]
    {x y z : Obj f} (α : x ⟶ y) (β : y ⟶ z) :
    forgetMap f (α ≫ β) = forgetMap f α ≫ forgetMap f β := rfl

/-- The structure functor sends a coherent sheaf over `g : T ⟶ B` to the
universe-lifted opposite category-of-elements point of `g`. -/
def forgetFunctor (f : X ⟶ B) [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩)
  map α := forgetMap f α
  map_id := forgetMap_id f
  map_comp := forgetMap_comp f

end StructureFunctor

/-- Objectwise, `forgetFunctor` is the universe-lifted opposite element of the
structure morphism `g : T ⟶ B`. -/
theorem forgetFunctor_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (forgetFunctor f).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := rfl

/-- `forgetFunctor` lies strictly over `Over S`. -/
theorem forgetFunctor_p (f : X ⟶ B) [FinitePresentation f] :
    forgetFunctor f ⋙ Classifying.toGroupoidsProjection B = p f := rfl

/-- The structure 1-morphism `CohStack f ⟶ B` of groupoid fibrations over
`Over S`. -/
def forget (f : X ⟶ B) [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f))

/-- Forgetting `forget` to based functors recovers `BasedFunctor.ofFunctor` of
`forgetFunctor`. -/
theorem forget.toBasedFunctor (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toBasedFunctor (forget f) =
      BasedFunctor.ofFunctor (forgetFunctor f) (forgetFunctor_p f) := rfl

/-- The structure morphism lies strictly over `Over S`. -/
theorem forget_p (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.toFunctor (forget f) ⋙
        Classifying.toGroupoidsProjection B =
      p f := forgetFunctor_p f

/-- On objects, `forget` sends `(T, g, F)` to the functor-of-points element of
`g`. -/
theorem forget_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (FiberedCategoryOver.Groupoids.toFunctor (forget f)).obj x =
      ULiftHom.objUp (op ⟨op x.σ.left, yonedaEquiv x.σ.hom⟩) := rfl

/-- The canonical structure morphism is compatible with every morphism of
lifted groupoid fibrations over a scheme. -/
theorem toIdentitySlice_comp {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    toIdentitySlice X = f ≫ toIdentitySlice Y := by
  have based_ext {F G :
      X.toBasedCategory ⥤ᵇ (Classifying.slice (Over.mk (𝟙 S))).toBasedCategory}
      (h : F.toFunctor = G.toFunctor) : F = G := by
    cases F
    cases G
    cases h
    rfl
  let P := Classifying.sliceProjection (Over.mk (𝟙 S))
  haveI : P.Faithful := by
    constructor
    intro a b g h e
    apply ULift.ext
    apply Over.OverMorphism.ext
    exact e
  have obj_injective : Function.Injective P.obj := by
    intro a b e
    change a.objDown.left = b.objDown.left at e
    have h : a.objDown = b.objDown :=
      CostructuredArrow.obj_ext _ _ e (Over.mkIdTerminal.hom_ext _ _)
    exact congrArg ULiftHom.objUp h
  apply Bicategory.InducedBicategory.hom_ext
  apply based_ext
  let F : X.total ⥤ ULiftHom.{u + 1} (Over (Over.mk (𝟙 S))) :=
    FiberedCategoryOver.Groupoids.toFunctor (toIdentitySlice X)
  let G : X.total ⥤ ULiftHom.{u + 1} (Over (Over.mk (𝟙 S))) :=
    FiberedCategoryOver.Groupoids.toFunctor (f ≫ toIdentitySlice Y)
  have h : F ⋙ P = G ⋙ P :=
    (FiberedCategoryOver.Groupoids.comm (toIdentitySlice X)).trans
      (FiberedCategoryOver.Groupoids.comm (f ≫ toIdentitySlice Y)).symm
  change F = G
  refine CategoryTheory.Functor.ext (F := F) (G := G)
    (fun x ↦ obj_injective (Functor.congr_obj h x)) ?_
  intro a b α
  apply P.map_injective
  rw [P.map_comp, P.map_comp, eqToHom_map, eqToHom_map]
  exact CategoryTheory.Functor.congr_hom h α

end AlgebraicGeometry.AlgebraicSpace.CohStack
