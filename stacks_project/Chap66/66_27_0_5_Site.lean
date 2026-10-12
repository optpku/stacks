/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Affine étale restriction

An étale morphism `f : X ⟶ Y` of algebraic spaces induces postcomposition
`affineEtaleSite X ⥤ affineEtaleSite Y` on affine étale sites, wrapping
`etaleRestriction` on the underlying small étale objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Postcomposition with an étale morphism `f : X ⟶ Y` sends affine schemes étale over `X`
to affine schemes étale over `Y`. -/
def affineEtaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    affineEtaleSite X ⥤ affineEtaleSite Y where
  obj U :=
    { obj := (etaleRestriction f).obj U.obj
      property := sorry }
  map g := ObjectProperty.homMk ((etaleRestriction f).map g.hom)
  map_id := sorry
  map_comp := sorry

/-- The object map of `affineEtaleRestriction f` is `etaleRestriction f` on the underlying
small étale object. -/
@[simp]
theorem affineEtaleRestriction_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (U : affineEtaleSite X) :
    ((affineEtaleRestriction f).obj U).obj = (etaleRestriction f).obj U.obj :=
  rfl

/-- The morphism map of `affineEtaleRestriction f` is `etaleRestriction f` on the underlying
small étale morphism. -/
@[simp]
theorem affineEtaleRestriction_map {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U V : affineEtaleSite X} (g : U ⟶ V) :
    ((affineEtaleRestriction f).map g).hom = (etaleRestriction f).map g.hom :=
  rfl

/-- Postcomposition on affine étale sites preserves the underlying scheme over `S`. -/
@[simp]
theorem affineEtaleRestriction_obj_left {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (U : affineEtaleSite X) :
    ((affineEtaleRestriction f).obj U).obj.left = U.obj.left :=
  rfl

/-- Postcomposition with an étale morphism is continuous for the affine étale topologies. -/
instance affineEtaleRestriction.instIsContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (affineEtaleRestriction f).IsContinuous (affineEtaleTopology X) (affineEtaleTopology Y) :=
  sorry

/-- Postcomposition with an étale morphism is cocontinuous for the affine étale topologies. -/
instance affineEtaleRestriction.instIsCocontinuous {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (affineEtaleRestriction f).IsCocontinuous (affineEtaleTopology X) (affineEtaleTopology Y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
