/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap96.Definition_96_24_1_Affine

/-!
# Affine projection of a category fibred in groupoids

A category fibred in groupoids `X` over `(Sch/S)_fppf` restricts to a functor
`X.Affine ⥤ S.AffineOver` landing in affine schemes over `S`. This is the
projection along which `𝒳_affine` inherits sites from `(Aff/S)_τ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The restricted projection `𝒳_affine ⟶ (Aff/S)` sending an object of `X`
lying over an affine scheme to that affine scheme over `S`. -/
def affineProjection (X : GroupoidsOver S) : Affine X ⥤ S.AffineOver where
  obj x := Scheme.AffineOver.mk (X.p.obj x.obj).left x.property (X.p.obj x.obj).hom
  map f := Scheme.AffineOver.homMk (X.p.map f.hom).left (Over.w (X.p.map f.hom))
  map_id := sorry
  map_comp := sorry

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

end AlgebraicGeometry.GroupoidsOver
