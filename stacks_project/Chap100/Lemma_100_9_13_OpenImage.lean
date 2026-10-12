/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Open image of an atlas open immersion

Given a surjective smooth atlas `p : U.toGroupoids ⟶ X` from an algebraic space
and an open immersion `i : V ⟶ U`, the open image is the strictly full
subcategory of objects of `X` whose pullback of `V ⟶ X` is surjective. This is
the canonical open substack of `X` through which `V ⟶ X` factors by a
surjective smooth morphism.
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

/-- The slice-level source condition: the projection
`V ×_{X, y} T ⟶ T` is a surjective 1-morphism of groupoid fibrations. -/
def openImageMem (p : U.toGroupoids ⟶ X) (i : V ⟶ U) {T : Over S}
    (y : GroupoidsOver.slice T ⟶ X) : Prop :=
  Groupoids.Hom.Surjective
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} y
      (AlgebraicSpace.toGroupoids.map i ≫ p))

/-- The full subcategory of `X.total` on objects `y` for which
`V ×_{X, y} T ⟶ T` is surjective, where `T` is the scheme of `y`. -/
def openImageObjects (p : U.toGroupoids ⟶ X) (i : V ⟶ U) :
    ObjectProperty X.total :=
  fun y ↦ openImageMem p i
    (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y)))

/-- A total object of `X` lies in `openImageObjects p i` if and only if the
Yoneda representative satisfies `openImageMem p i`. -/
theorem mem_openImageObjects (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    (y : X.total) :
    openImageObjects p i y ↔
      openImageMem p i
        (YonedaSlice.representative (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y))) :=
  sorry

/-- The restricted projection of `openImageObjects p i` remains fibred in
groupoids. -/
instance instIsFiberedInGroupoids_openImageObjects (p : U.toGroupoids ⟶ X)
    (i : V ⟶ U) [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Functor.IsFibered.InGroupoids ((openImageObjects p i).ι ⋙ X.p) :=
  sorry

/-- The full subcategory of objects with surjective pullback of `V ⟶ X` is an
algebraic stack. -/
instance instAlgebraicStack_openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    AlgebraicStack (ofFunctor ((openImageObjects p i).ι ⋙ X.p)) :=
  sorry

/-- The inclusion of `openImageObjects p i` is an open immersion. -/
instance instOpenImmersion_openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    OpenImmersion (inclusionOf X (openImageObjects p i)) :=
  sorry

/-- The composite of an open immersion of algebraic spaces with a smooth atlas
is a smooth 1-morphism of groupoid fibrations. -/
instance instSmooth_toGroupoids_map_comp (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Smooth (AlgebraicSpace.toGroupoids.map i ≫ p) :=
  sorry

/-- Objects of `V.toGroupoids` lie in `openImageObjects p i`, so the composite
`V ⟶ X` lifts through the full subcategory. -/
theorem toGroupoids_map_comp_obj_mem_openImageObjects (p : U.toGroupoids ⟶ X)
    (i : V ⟶ U) [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] (y : V.toGroupoids.total) :
    openImageObjects p i
      ((toFunctor (AlgebraicSpace.toGroupoids.map i ≫ p)).obj y) :=
  sorry

/-- The canonical open substack of `X` associated to an open of a surjective
smooth atlas: objects whose pullback of `V ⟶ X` is surjective. -/
def openImage (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i] :
    OpenSubstack X :=
  OpenSubstack.ofι (inclusionOf X (openImageObjects p i))

/-- `openImage p i` is an algebraic stack with a strictly full open immersion
into `X`. -/
theorem openImage_spec (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    AlgebraicStack (openImage p i).Y ∧ OpenImmersion (openImage p i).ι ∧
      IsStrictlyFull (openImage p i).ι :=
  sorry

/-- The canonical factorization `V.toGroupoids ⟶ (openImage p i).Y` of
`AlgebraicSpace.toGroupoids.map i ≫ p` through the open image. -/
def openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    V.toGroupoids ⟶ (openImage p i).Y :=
  ofBasedFunctor
    { toFunctor := (openImageObjects p i).lift
        (toFunctor (AlgebraicSpace.toGroupoids.map i ≫ p))
        fun y ↦ toGroupoids_map_comp_obj_mem_openImageObjects p i y
      w := sorry }

/-- The factorization `openImageHom p i` recovers the composite `V ⟶ X`. -/
theorem openImageHom_comp (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    openImageHom p i ≫ (openImage p i).ι =
      AlgebraicSpace.toGroupoids.map i ≫ p :=
  sorry

/-- The factored atlas `openImageHom p i` is smooth. -/
instance instSmooth_openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Smooth (openImageHom p i) :=
  sorry

/-- The factored atlas `openImageHom p i` is surjective. -/
instance instSurjective_openImageHom (p : U.toGroupoids ⟶ X) (i : V ⟶ U)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Surjective (openImageHom p i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
