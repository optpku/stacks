/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

/-- The morphism between relative projective-line families induced by a morphism over the
base. -/
noncomputable def map {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    space X' ⟶ space X :=
  pullback.map X'.hom (ProjectiveSpace.toBase 1 S)
    X.hom (ProjectiveSpace.toBase 1 S) g.left (𝟙 _) (𝟙 _)
    ((Category.comp_id X'.hom).trans (Over.w g).symm)
    ((Category.comp_id (ProjectiveSpace.toBase 1 S)).trans
      (Category.id_comp (ProjectiveSpace.toBase 1 S)).symm)

/-- The first projection of `map g` is the first projection followed by `g`. -/
theorem map_fst {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    map g ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) =
      pullback.fst X'.hom (ProjectiveSpace.toBase 1 S) ≫ g.left := by
  simp only [map, pullback.map, pullback.lift_fst]

/-- The second projection of `map g` is the second projection. -/
theorem map_snd {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    map g ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) =
      pullback.snd X'.hom (ProjectiveSpace.toBase 1 S) := by
  simp only [map, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The relative projective-line family is cartesian with respect to change of its first
factor. -/
theorem map_isPullback {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    IsPullback (map g) (pullback.fst X'.hom (ProjectiveSpace.toBase 1 S))
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S)) g.left := by
  refine IsPullback.of_right ?_ (map_fst g)
    (IsPullback.of_hasPullback X.hom (ProjectiveSpace.toBase 1 S)).flip
  rw [map_snd, Over.w]
  exact (IsPullback.of_hasPullback X'.hom (ProjectiveSpace.toBase 1 S)).flip

/-- The projective-line-family map induced by the identity is the identity. -/
theorem map_id {S : Scheme.{u}} (X : Over S) :
    map (𝟙 X) = 𝟙 (space X) := by
  apply pullback.hom_ext <;> simp [map]

/-- Projective-line-family maps respect composition. -/
theorem map_comp {S : Scheme.{u}} {X X' X'' : Over S}
    (h : X'' ⟶ X') (g : X' ⟶ X) :
    map (h ≫ g) = map h ≫ map g := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, map_fst, map_snd, Over.comp_left] <;>
    simp only [← Category.assoc, map_fst]

/-- The inverse image in a compactification of the projective-line family over a
closed subscheme. -/
def deformationCenterInclusion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    pullback b (ProjectiveLineFamily.map
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) ⟶ W :=
  pullback.fst b (ProjectiveLineFamily.map
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/-- `deformationCenterInclusion` is the first projection of its defining pullback. -/
theorem deformationCenterInclusion_def
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    deformationCenterInclusion i b = pullback.fst b (ProjectiveLineFamily.map
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) := rfl

/-- The deformation-center inclusion is a closed immersion. -/
instance deformationCenterInclusionIsClosedImmersion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) :
    IsClosedImmersion (deformationCenterInclusion i b) := by
  haveI : IsClosedImmersion (ProjectiveLineFamily.map
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (map_isPullback (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).flip
      ‹IsClosedImmersion i›
  dsimp [deformationCenterInclusion]
  infer_instance

end AlgebraicGeometry.ProjectiveLineFamily
