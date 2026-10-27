/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Associated affine site of a category fibred in groupoids

The associated affine site of a category fibred in groupoids `X` over
`(Sch/S)_fppf` is the full subcategory of objects lying over an affine scheme,
equipped with the chaotic topology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Objects of a category fibred in groupoids that lie over an affine scheme. -/
def affineObjects (X : GroupoidsOver S) : ObjectProperty X.total :=
  (Scheme.affineOverProperty S).inverseImage X.p

/-- An object of `X` lies in `affineObjects X` if and only if the scheme it
lies over is affine. -/
theorem mem_affineObjects_iff (X : GroupoidsOver S) (x : X.total) :
    affineObjects X x ↔ IsAffine (X.p.obj x).left :=
  sorry

/-- The full subcategory `𝒳_affine` of objects of `X` lying over an affine
scheme. -/
abbrev Affine (X : GroupoidsOver S) :=
  (affineObjects X).FullSubcategory

/-- The inclusion of the associated affine site into the total category of
`X`. -/
abbrev affineInclusion (X : GroupoidsOver S) : Affine X ⥤ X.total :=
  (affineObjects X).ι

/-- Every object of the associated affine site lies over an affine scheme. -/
instance instIsAffine (X : GroupoidsOver S) (x : Affine X) :
    IsAffine (X.p.obj x.obj).left :=
  x.property

/-- Construct an object of the associated affine site from an object of `X`
lying over an affine scheme. -/
def Affine.mk {X : GroupoidsOver S} (x : X.total)
    (hx : IsAffine (X.p.obj x).left) : Affine X :=
  ⟨x, hx⟩

/-- The underlying object of `Affine.mk x hx` is `x`. -/
theorem Affine.mk_obj {X : GroupoidsOver S} (x : X.total)
    (hx : IsAffine (X.p.obj x).left) : (Affine.mk x hx).obj = x :=
  sorry

/-- The chaotic topology on the associated affine site of `X`. -/
abbrev affineTopology (X : GroupoidsOver S) : GrothendieckTopology (Affine X) :=
  ⊥

/-- The topology of the associated affine site is the chaotic topology. -/
theorem affineTopology_eq_bot (X : GroupoidsOver S) :
    affineTopology X = ⊥ :=
  sorry

noncomputable section

/-- The restricted projection `𝒳_affine ⟶ (Aff/S)` sending an object of `X`
lying over an affine scheme to that affine scheme over `S`. -/
def affineProjection (X : GroupoidsOver S) : Affine X ⥤ S.AffineOver where
  obj x := Scheme.AffineOver.mk (X.p.obj x.obj).left x.property (X.p.obj x.obj).hom
  map f := Scheme.AffineOver.homMk (X.p.map f.hom).left (Over.w (X.p.map f.hom))
  map_id x := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply InducedCategory.hom_ext
    change (X.p.map (𝟙 x.obj)).left = 𝟙 (X.p.obj x.obj).left
    rw [X.p.map_id]
    rfl
  map_comp f g := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply InducedCategory.hom_ext
    change (X.p.map (f.hom ≫ g.hom)).left =
      (X.p.map f.hom).left ≫ (X.p.map g.hom).left
    rw [X.p.map_comp]
    rfl

/-- The object map of `affineProjection X` is `Scheme.AffineOver.mk` of the
underlying affine scheme and structure morphism. -/
theorem affineProjection_obj (X : GroupoidsOver S) (x : Affine X) :
    (affineProjection X).obj x =
      Scheme.AffineOver.mk (X.p.obj x.obj).left x.property (X.p.obj x.obj).hom :=
  sorry

/-- The scheme morphism underlying `affineProjection X` applied to `f` is the
scheme morphism underlying `X.p.map f.hom`. -/
theorem affineProjection_map (X : GroupoidsOver S) {x y : Affine X} (f : x ⟶ y) :
    (Scheme.AffineOver.toScheme S).map ((affineProjection X).map f) =
      (X.p.map f.hom).left :=
  sorry

/-- Forgetting from affine schemes over `S` after `affineProjection X` recovers
the composite of the affine inclusion with the original projection of `X`. -/
theorem affineProjection_comp_forget (X : GroupoidsOver S) :
    affineProjection X ⋙ Scheme.AffineOver.forget S =
      affineInclusion X ⋙ X.p :=
  sorry

/-- The restricted projection `𝒳_affine ⟶ (Aff/S)` is fibred in groupoids. -/
instance affineProjection_isFiberedInGroupoids (X : GroupoidsOver S) :
    Functor.IsFibered.InGroupoids (affineProjection X) :=
  sorry

end

end AlgebraicGeometry.GroupoidsOver
