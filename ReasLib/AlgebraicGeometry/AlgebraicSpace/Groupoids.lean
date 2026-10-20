/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Slice

/-!
# Groupoid fibrations associated to algebraic spaces

The discrete Grothendieck construction associates a groupoid fibration to an
algebraic space. For a scheme, it is canonically equivalent to the slice fibration.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver BasedFunctor BasedNatIso
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- The category fibred in groupoids associated to an algebraic space, obtained by
applying the discrete Grothendieck construction to its functor of points and
forgetting from sets to groupoids. -/
def toGroupoids {S : Scheme.{u}} (F : AlgebraicSpace S) : GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints)

/-- A morphism of algebraic spaces induces a 1-morphism of the associated
categories fibred in groupoids. -/
def toGroupoids.map {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    F.toGroupoids ⟶ G.toGroupoids :=
  (Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map f)

/-- The groupoid fibration of an algebraic space is the discrete Grothendieck
construction of its functor of points, forgotten to groupoids. -/
theorem toGroupoids_spec {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F.toGroupoids =
      (Sets.toGroupoids (Over S)).obj
        ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints) := sorry

/-- The projection of `toGroupoids F` is the opposite category-of-elements
projection of the functor of points. -/
theorem toGroupoids_p {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F.toGroupoids.p = ((Sets.ofPresheaf (Over S)).obj F.functorOfPoints).p := sorry

/-- `toGroupoids.map` sends identity morphisms of algebraic spaces to identity
1-morphisms. -/
theorem toGroupoids.map_id {S : Scheme.{u}} (F : AlgebraicSpace S) :
    toGroupoids.map (𝟙 F) = 𝟙 F.toGroupoids := sorry

/-- The groupoid fibration of a scheme over `S` is canonically equivalent to the
slice fibration, by applying `Sets.toGroupoids` to the set-fibred comparison of
`ofPresheaf (yoneda.obj U)` with `Sets.slice U`. -/
def ofOverSliceEquiv {S : Scheme.{u}} (U : Over S) :
    (ofOver U).toGroupoids ≌ GroupoidsOver.slice U :=
  let homBF :
      BasedFunctor
        ((Sets.ofPresheaf (Over S)).obj (yoneda.obj U)).toBasedCategory
        (Sets.slice U).toBasedCategory :=
    { obj := fun x ↦ Over.mk x.unop.2
      map := fun f ↦ Over.homMk f.unop.1.unop sorry
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let invBF :
      BasedFunctor (Sets.slice U).toBasedCategory
        ((Sets.ofPresheaf (Over S)).obj (yoneda.obj U)).toBasedCategory :=
    { obj := fun α ↦ Opposite.op ⟨Opposite.op α.left, α.hom⟩
      map := fun {α β} κ ↦
        Quiver.Hom.op
          (CategoryOfElements.homMk
            (⟨Opposite.op β.left, β.hom⟩ : (yoneda.obj U).Elements)
            (⟨Opposite.op α.left, α.hom⟩ : (yoneda.obj U).Elements)
            κ.left.op sorry)
      map_id := sorry
      map_comp := sorry
      w := sorry }
  let qi : BasedFunctor.QuasiInverse homBF :=
    { inverse := invBF
      unitIso := BasedNatIso.ofComponents (fun x ↦ Iso.refl _) sorry sorry
      counitIso := BasedNatIso.ofComponents (fun α ↦ Iso.refl _) sorry sorry }
  (Sets.toGroupoids (Over S)).mapEquivalence
    (Bicategory.InducedBicategory.equivalenceMk qi.toEquivalence)

/-- The unit of `ofOverSliceEquiv` identifies the composite of the comparison with
its inverse. -/
theorem ofOverSliceEquiv_hom {S : Scheme.{u}} (U : Over S) :
    Nonempty
      ((ofOverSliceEquiv U).hom ≫ (ofOverSliceEquiv U).inv ≅
        𝟙 (ofOver U).toGroupoids) := sorry

/-- The groupoid fibration of a scheme over `S` is equivalent to the canonical
slice fibration. -/
theorem toGroupoids_ofOver {S : Scheme.{u}} (U : Over S) :
    Nonempty ((ofOver U).toGroupoids ≌ GroupoidsOver.slice U) := sorry

end AlgebraicSpace

end AlgebraicGeometry
