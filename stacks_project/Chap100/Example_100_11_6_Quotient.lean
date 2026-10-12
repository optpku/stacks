/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap65.Lemma_65_14_3_Relation
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Example_100_11_6_Cover

/-!
# Fppf quotient of the Galois pullback

This module records the algebraic space `X = U / G` as the fppf quotient sheaf of
`ofAut action`, converts it to a groupoid fibration over `Spec algebraicQ`, and
packages the composite `Spec algebraicQ ⟶ U ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open FiberedCategoryOver
open FiberedCategoryOver.Groupoids (overMap ofBasedFunctor toFunctor)
open scoped Bicategory

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GaloisPullback

/-- The fppf sheaf `X = U / G`, obtained by sheafifying the universe-raised
quotient presheaf of `ofAut action`. -/
def sheafOfPoints : Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  (ofAut action).quotientSheaf (Scheme.fppfTopology.over base)

/-- `sheafOfPoints` is the fppf quotient sheaf of the Galois pre-relation
`ofAut action`. -/
theorem sheafOfPoints_eq :
    sheafOfPoints = (ofAut action).quotientSheaf (Scheme.fppfTopology.over base) :=
  sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical
quotient map. -/
def atlas :
    (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover ⟶ sheafOfPoints :=
  (ofAut action).quotientMap (Scheme.fppfTopology.over base)

/-- The atlas is the canonical fppf quotient map of `ofAut action`. -/
theorem atlas_eq :
    atlas = (ofAut action).quotientMap (Scheme.fppfTopology.over base) := sorry

/-- The fppf quotient sheaf `X = U / G` is an algebraic space over
`Spec algebraicQ` in the `uliftYoneda` sense of Spaces, Definition 65.14.4. -/
theorem sheafOfPoints_spec :
    uliftYoneda.{1}.relativelyRepresentable (diag sheafOfPoints.obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{1} atlas.hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) atlas.hom :=
  sorry

/-- Convert a `Type 1` presheaf on schemes over `Spec algebraicQ` to a groupoid
fibration by the discrete Grothendieck construction. -/
def sheafToGroupoids (F : (Over base)ᵒᵖ ⥤ Type 1) : GroupoidsOver base :=
  (Sets.toGroupoids (Over base)).obj ((Sets.ofPresheaf (Over base)).obj F)

/-- `sheafToGroupoids F` is `Sets.toGroupoids` of `Sets.ofPresheaf` applied to
`F`. -/
theorem sheafToGroupoids_eq (F : (Over base)ᵒᵖ ⥤ Type 1) :
    sheafToGroupoids F =
      (Sets.toGroupoids (Over base)).obj ((Sets.ofPresheaf (Over base)).obj F) :=
  sorry

/-- A morphism of `Type 1` presheaves induces a 1-morphism of the associated
groupoid fibrations. -/
def sheafToGroupoidsMap {F G : (Over base)ᵒᵖ ⥤ Type 1} (α : F ⟶ G) :
    sheafToGroupoids F ⟶ sheafToGroupoids G :=
  (Sets.toGroupoids (Over base)).map ((Sets.ofPresheaf (Over base)).map α)

/-- `sheafToGroupoidsMap α` is `Sets.toGroupoids.map` of `Sets.ofPresheaf.map α`. -/
theorem sheafToGroupoidsMap_eq {F G : (Over base)ᵒᵖ ⥤ Type 1} (α : F ⟶ G) :
    sheafToGroupoidsMap α =
      (Sets.toGroupoids (Over base)).map ((Sets.ofPresheaf (Over base)).map α) :=
  sorry

/-- The algebraic space `X = U / G` as a category fibred in groupoids over
`Spec algebraicQ`. -/
def toStack : GroupoidsOver base := sheafToGroupoids sheafOfPoints.obj

/-- `toStack` is the groupoid fibration associated to `sheafOfPoints`. -/
theorem toStack_spec : toStack = sheafToGroupoids sheafOfPoints.obj := sorry

/-- The universe-raised representable sheaf of the cover, as a groupoid
fibration. -/
def coverToStack : GroupoidsOver base :=
  sheafToGroupoids ((Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover).obj

/-- `coverToStack` is the groupoid fibration of the `uliftYoneda` sheaf of
`cover`. -/
theorem coverToStack_eq :
    coverToStack =
      sheafToGroupoids
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover).obj :=
  sorry

/-- The atlas `U ⟶ X` as a 1-morphism of groupoid fibrations. -/
def atlasHom : coverToStack ⟶ toStack := sheafToGroupoidsMap atlas.hom

/-- `atlasHom` is `sheafToGroupoidsMap` of the sheaf atlas. -/
theorem atlasHom_eq : atlasHom = sheafToGroupoidsMap atlas.hom := sorry

/-- The universe-raised representable presheaf of the cover. -/
abbrev coverPresheaf : (Over base)ᵒᵖ ⥤ Type 1 :=
  ((Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover).obj

/-- `coverPresheaf` is the underlying presheaf of `uliftYoneda.obj cover`. -/
theorem coverPresheaf_eq :
    coverPresheaf =
      ((Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover).obj := sorry

/-- Compatibility of a morphism in `Over cover` with the `uliftYoneda` action on
the cover presheaf. -/
theorem sliceToCover_map_condition {α β : Over cover} (κ : α ⟶ β) :
    coverPresheaf.map κ.left.op (ULift.up β.hom) = ULift.up α.hom := sorry

/-- The comparison `GroupoidsOver.slice cover ⟶ coverToStack` sending a test
object `α` to the `uliftYoneda` section `ULift.up α.hom`. -/
def sliceToCover : GroupoidsOver.slice cover ⟶ coverToStack :=
  ofBasedFunctor
    { obj := fun α : Over cover ↦
        (Opposite.op ⟨Opposite.op α.left, ULift.up α.hom⟩ : coverPresheaf.Elementsᵒᵖ)
      map := fun {α β} κ ↦
        Quiver.Hom.op
          (CategoryOfElements.homMk
            (⟨Opposite.op β.left, ULift.up β.hom⟩ : coverPresheaf.Elements)
            (⟨Opposite.op α.left, ULift.up α.hom⟩ : coverPresheaf.Elements)
            κ.left.op (sliceToCover_map_condition κ))
      map_id := sorry
      map_comp := sorry
      w := sorry }

/-- `sliceToCover` sends a test object `α` to the opposite `uliftYoneda` section
determined by `α.hom`. -/
theorem sliceToCover_obj (α : Over cover) :
    (toFunctor sliceToCover).obj α =
      Opposite.op ⟨Opposite.op α.left, ULift.up α.hom⟩ := sorry

/-- The composite `Spec algebraicQ ⟶ U ⟶ X` as a 1-morphism of groupoid
fibrations over `Spec algebraicQ`. -/
def pointHom : GroupoidsOver.slice (Over.mk (𝟙 base)) ⟶ toStack :=
  overMap sectionHom ≫ sliceToCover ≫ atlasHom

/-- `pointHom` is `overMap` of the diagonal section, followed by the atlas. -/
theorem pointHom_eq :
    pointHom = overMap sectionHom ≫ sliceToCover ≫ atlasHom := sorry

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
