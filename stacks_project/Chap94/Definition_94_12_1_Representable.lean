/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Categories fibred in groupoids representable by algebraic spaces

An algebraic space over a scheme `S` determines a category fibred in groupoids
over `Over S` by the discrete Grothendieck construction of its functor of points.
A morphism of such fibrations is representable by algebraic spaces when every
slice base change is equivalent to an algebraic space over `S` mapping to the
test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver BasedFunctor BasedNatIso
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids.map :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S},
    (F ⟶ G) → (F.toGroupoids ⟶ G.toGroupoids))

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids_spec :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    F.toGroupoids =
      (Sets.toGroupoids (Over S)).obj
        ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints))

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids_p :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    F.toGroupoids.p = ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints).p)

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids.map_id :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    toGroupoids.map (𝟙 F) = 𝟙 F.toGroupoids)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverSliceEquiv :
  ∀ {S : Scheme.{u}} (U : Over S),
    (ofOver U).toGroupoids ≌ GroupoidsOver.slice U)

#check (AlgebraicGeometry.AlgebraicSpace.ofOverSliceEquiv_hom :
  ∀ {S : Scheme.{u}} (U : Over S),
    Nonempty
      ((ofOverSliceEquiv U).hom ≫ (ofOverSliceEquiv U).inv ≅
        𝟙 (ofOver U).toGroupoids))

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids_ofOver :
  ∀ {S : Scheme.{u}} (U : Over S),
    Nonempty ((ofOver U).toGroupoids ≌ GroupoidsOver.slice U))

end AlgebraicSpace

open AlgebraicSpace

#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace :
  ∀ {S : Scheme.{u}},
    ObjectProperty (GroupoidsOver S))

#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.iff_exists_equivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    IsRepresentableByAlgebraicSpace X ↔
      ∃ F : AlgebraicSpace S, Nonempty (X ≌ F.toGroupoids))

#check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.of_toGroupoids :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    IsRepresentableByAlgebraicSpace F.toGroupoids)

#check (AlgebraicGeometry.RepresentsBaseChange :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    (X ⟶ Y) → ∀ {U : Over S}, (GroupoidsOver.slice U ⟶ Y) →
      ∀ (Fy : AlgebraicSpace S), (Fy ⟶ ofOver U) → Prop)

#check (AlgebraicGeometry.RepresentsBaseChange.apex_equivalence :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U},
    RepresentsBaseChange f y Fy fy → Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids))

#check (AlgebraicGeometry.RepresentsBaseChange.projection_triangle :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U},
    RepresentsBaseChange f y Fy fy → ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f))

section

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces :
  MorphismProperty (GroupoidsOver S))

end

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
        ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
          RepresentsBaseChange f y Fy fy)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.exists_represents :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f → ∀ {U : Over S}
      (y : GroupoidsOver.slice U ⟶ Y), ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
      RepresentsBaseChange f y Fy fy)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_represents :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y},
    (∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        RepresentsBaseChange f y Fy fy) → relativelyRepresentableByAlgebraicSpaces f)

end AlgebraicGeometry
