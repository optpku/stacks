/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily

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
      pullback.fst X'.hom (ProjectiveSpace.toBase 1 S) ≫ g.left := sorry

/-- The second projection of `map g` is the second projection. -/
theorem map_snd {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    map g ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) =
      pullback.snd X'.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The relative projective-line family is cartesian with respect to change of its first
factor. -/
theorem map_isPullback {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X) :
    IsPullback (map g) (pullback.fst X'.hom (ProjectiveSpace.toBase 1 S))
      (pullback.fst X.hom (ProjectiveSpace.toBase 1 S)) g.left := sorry

/-- The projective-line-family map induced by the identity is the identity. -/
theorem map_id {S : Scheme.{u}} (X : Over S) :
    map (𝟙 X) = 𝟙 (space X) := sorry

/-- Projective-line-family maps respect composition. -/
theorem map_comp {S : Scheme.{u}} {X X' X'' : Over S}
    (h : X'' ⟶ X') (g : X' ⟶ X) :
    map (h ≫ g) = map h ≫ map g := sorry

end AlgebraicGeometry.ProjectiveLineFamily
