/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

/-!
# Open image of an atlas open immersion

An open of a smooth surjective algebraic-space atlas determines the full
subcategory of objects whose pullback of that open is surjective. This is an
algebraic open substack, and the restricted atlas factors through it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {U V : AlgebraicSpace S}

/-- The projection `V ×_{X, y} T ⟶ T` is a surjective morphism of groupoid
fibrations. -/
def openImageMem (p : U.toGroupoids ⟶ X) (i : V ⟶ U) {T : Over S}
    (y : GroupoidsOver.slice T ⟶ X) : Prop :=
  Groupoids.Hom.Surjective
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} y
      (AlgebraicSpace.toGroupoids.map i ≫ p))

/-- The object property selecting objects of `X` whose pullback of `V ⟶ X`
is surjective over their base scheme. -/
def openImageObjects (p : U.toGroupoids ⟶ X) (i : V ⟶ U) :
    ObjectProperty X.total :=
  fun y ↦ openImageMem p i
    (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y)))

/-- An object belongs to the open image exactly when its Yoneda representative
has surjective pullback of `V ⟶ X`. -/
theorem mem_openImageObjects (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    (y : X.total) :
    openImageObjects p i y ↔
      openImageMem p i
        (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y))) :=
  Iff.rfl

/-- The projection restricted to objects with surjective pullback of an open
of a smooth surjective atlas is fibred in groupoids. -/
instance instIsFiberedInGroupoids_openImageObjects (p : U.toGroupoids ⟶ X)
    (i : V ⟶ U) [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Functor.IsFibered.InGroupoids ((openImageObjects p i).ι ⋙ X.p) :=
  sorry

/-- The groupoid fibration on objects with surjective pullback of an open
of a smooth surjective atlas. -/
def openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i] :
    GroupoidsOver S :=
  Substack.category X (openImageObjects p i)
    (instIsFiberedInGroupoids_openImageObjects p i)

/-- The literal inclusion of the open-image groupoid fibration into `X`. -/
def openImageι (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i] :
    openImage p i ⟶ X :=
  Substack.inclusion X (openImageObjects p i)
    (instIsFiberedInGroupoids_openImageObjects p i)

/-- The open image of an open of a smooth surjective atlas is an algebraic stack. -/
instance instAlgebraicStack_openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    AlgebraicStack (openImage p i) :=
  sorry

/-- The literal inclusion of the open image into its ambient stack is an open immersion. -/
instance instOpenImmersion_openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    OpenImmersion (openImageι p i) :=
  sorry

/-- The composite of an open immersion of algebraic spaces with a smooth
morphism to a stack is smooth. -/
instance instSmooth_toGroupoids_map_comp (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Smooth (AlgebraicSpace.toGroupoids.map i ≫ p) :=
  sorry

/-- The composite `V ⟶ X` takes each object into the full subcategory with
surjective pullback of `V ⟶ X`. -/
theorem toGroupoids_map_comp_obj_mem_openImageObjects (p : U.toGroupoids ⟶ X)
    (i : V ⟶ U) [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] (y : V.toGroupoids.total) :
    openImageObjects p i
      ((toFunctor (AlgebraicSpace.toGroupoids.map i ≫ p)).obj y) :=
  sorry

/-- The objects with surjective pullback of an open of a smooth surjective
atlas form a replete algebraic open substack. -/
theorem openImage_spec (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Substack.IsOpen X (openImageObjects p i) :=
  sorry

/-- The lift of the composite `V ⟶ X` to the full subcategory defining its open image. -/
def openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    V.toGroupoids ⟶ openImage p i :=
  ofBasedFunctor
    { toFunctor := (openImageObjects p i).lift
        (toFunctor (AlgebraicSpace.toGroupoids.map i ≫ p))
        fun y ↦ toGroupoids_map_comp_obj_mem_openImageObjects p i y
      w := sorry }

/-- Composing the lifted atlas with the open-image inclusion recovers `V ⟶ X`. -/
theorem openImageHom_comp (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    openImageHom p i ≫ openImageι p i =
      AlgebraicSpace.toGroupoids.map i ≫ p :=
  sorry

/-- The lifted atlas of the open image is smooth. -/
instance instSmooth_openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Smooth (openImageHom p i) :=
  sorry

/-- The lifted atlas of the open image is surjective. -/
instance instSurjective_openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Surjective (openImageHom p i) :=
  sorry

/-- An open of a smooth surjective algebraic-space atlas factors through an
algebraic open substack by a smooth surjective morphism. -/
theorem exists_openSubstack_of_openImmersion {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {U V : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i] :
    ∃ (Y : GroupoidsOver S) (j : Y ⟶ X) (q : V.toGroupoids ⟶ Y),
      AlgebraicStack Y ∧ Groupoids.Hom.OpenImmersion j ∧
        Groupoids.Hom.Smooth q ∧ Groupoids.Hom.Surjective q ∧
          q ≫ j = AlgebraicSpace.toGroupoids.map i ≫ p :=
  sorry

end AlgebraicGeometry.AlgebraicStack
