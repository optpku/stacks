/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange

/-!
# Categories fibred in groupoids representable by algebraic spaces

Representability identifies a groupoid fibration with an algebraic space.
Relative representability includes the projection triangle of every slice base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

open AlgebraicSpace

/-- A category fibred in groupoids over `(Sch/S)_fppf` is representable by an
algebraic space over `S` when it is equivalent to the Grothendieck construction
of some algebraic space over `S`. -/
def IsRepresentableByAlgebraicSpace {S : Scheme.{u}} :
    ObjectProperty (GroupoidsOver S) :=
  fun X ↦ ∃ F : AlgebraicSpace S, Nonempty (X ≌ F.toGroupoids)

/-- A representing algebraic space selected from a supplied representability witness. -/
noncomputable def IsRepresentableByAlgebraicSpace.representingSpace
    {S : Scheme.{u}} {Y : GroupoidsOver S} (hY : IsRepresentableByAlgebraicSpace Y) :
    AlgebraicSpace S := Classical.choose hY

/-- The equivalence supplied by the selected representation of a groupoid fibration. -/
noncomputable def IsRepresentableByAlgebraicSpace.representingEquiv
    {S : Scheme.{u}} {Y : GroupoidsOver S} (hY : IsRepresentableByAlgebraicSpace Y) :
    Y ≌ hY.representingSpace.toGroupoids := Classical.choice (Classical.choose_spec hY)

/-- The selected representing space presents the original groupoid fibration. -/
theorem IsRepresentableByAlgebraicSpace.representingSpace_spec
    {S : Scheme.{u}} {Y : GroupoidsOver S} (hY : IsRepresentableByAlgebraicSpace Y) :
    Nonempty (Y ≌ hY.representingSpace.toGroupoids) := ⟨hY.representingEquiv⟩

/-- Representability by an algebraic space is equivalent to the existence of an
algebraic space and a bicategorical equivalence to its groupoid fibration. -/
theorem IsRepresentableByAlgebraicSpace.iff_exists_equivalence
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsRepresentableByAlgebraicSpace X ↔
      ∃ F : AlgebraicSpace S, Nonempty (X ≌ F.toGroupoids) := sorry

/-- The groupoid fibration of an algebraic space is representable by that
algebraic space. -/
theorem IsRepresentableByAlgebraicSpace.of_toGroupoids
    {S : Scheme.{u}} (F : AlgebraicSpace S) :
    IsRepresentableByAlgebraicSpace F.toGroupoids := sorry

/-- A slice 2-fibre product of `f` along `y : GroupoidsOver.slice U ⟶ Y` is
represented by an algebraic space `Fy` over `S` with structure morphism
`fy : Fy ⟶ ofOver U` when the apex is equivalent to `Fy.toGroupoids` and the
projection triangle identifies `toGroupoids.map fy` with `TwoFibreProduct.fst`
along `ofOverSliceEquiv`. -/
def RepresentsBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
    (fy : Fy ⟶ ofOver U) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
    Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)

/-- A representing algebraic space is equivalent to the slice 2-fibre product. -/
theorem RepresentsBaseChange.apex_equivalence {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids) := sorry

/-- The structure morphism of a representing algebraic space recovers the
projection of the slice 2-fibre product along `ofOverSliceEquiv`. -/
theorem RepresentsBaseChange.projection_triangle {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S} {fy : Fy ⟶ ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ Fy.toGroupoids,
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f) :=
  sorry

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces when every base change along a morphism from a
canonical slice is representable by an algebraic space over `S`. -/
def relativelyRepresentableByAlgebraicSpaces {S : Scheme.{u}} :
    MorphismProperty (GroupoidsOver S) :=
  fun _ Y f ↦ ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
    ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U), RepresentsBaseChange f y Fy fy

/-- Relative representability by algebraic spaces means every slice base change
is represented by an algebraic space over `S`. -/
theorem relativelyRepresentableByAlgebraicSpaces.iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
        ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
          RepresentsBaseChange f y Fy fy := sorry

/-- A relatively representable 1-morphism has a representing algebraic space for
every slice test. -/
theorem relativelyRepresentableByAlgebraicSpaces.exists_represents {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) {U : Over S}
    (y : GroupoidsOver.slice U ⟶ Y) :
    ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
      RepresentsBaseChange f y Fy fy := sorry

/-- Relative representability by algebraic spaces follows from a representing
algebraic space for every slice test. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_represents {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        RepresentsBaseChange f y Fy fy) :
    relativelyRepresentableByAlgebraicSpaces f := sorry

end AlgebraicGeometry

