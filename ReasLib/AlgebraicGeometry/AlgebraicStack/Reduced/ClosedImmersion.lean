/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Reduced closed immersions of algebraic stacks

Every closed subset of an algebraic stack has a reduced closed-substack
structure, unique as an essential-image object property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor toBasedFunctor)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every closed subset of the points of an algebraic stack is the range of a
fully faithful reduced closed immersion, unique as an essential-image object
property. -/
theorem exists_reduced_closedImmersion {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (T : Set (Points X)) (hT : IsClosed T) :
    ∃ (Y : GroupoidsOver S) (_ : AlgebraicStack Y) (i : Y ⟶ X),
      Groupoids.Hom.ClosedImmersion i ∧
        (toFunctor i).Full ∧ (toFunctor i).Faithful ∧
          Set.range (Points.map i) = T ∧ IsReduced Y ∧
            ∀ (Z : GroupoidsOver S) [AlgebraicStack Z] (j : Z ⟶ X),
              Groupoids.Hom.ClosedImmersion j → Set.range (Points.map j) = T →
                IsReduced Z → (toFunctor j).essImage = (toFunctor i).essImage :=
  sorry

/-- Reduced closed immersions with the same range on points have the same
essential-image object property. -/
theorem reduced_closedImmersion_essImage_eq {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (i : Y ⟶ X) (j : Z ⟶ X)
    [Groupoids.Hom.ClosedImmersion i] [Groupoids.Hom.ClosedImmersion j]
    (hY : IsReduced Y) (hZ : IsReduced Z)
    (h_eq : Set.range (Points.map i) = Set.range (Points.map j)) :
    (toFunctor i).essImage = (toFunctor j).essImage :=
  by
    obtain ⟨W, hW, k, hk, _, _, _, _, huniq⟩ :=
      exists_reduced_closedImmersion (Set.range (Points.map i))
        (Points.isClosed_range_of_closedImmersion i)
    letI := hW
    letI := hk
    calc
      (toFunctor i).essImage = (toFunctor k).essImage :=
        huniq Y i inferInstance rfl hY
      _ = (toFunctor j).essImage :=
        (huniq Z j inferInstance h_eq.symm hZ).symm

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.Groupoids.Hom.ClosedImmersion

/-- A closed immersion into a reduced algebraic stack whose range on points is
the whole space is an equivalence over the base. -/
theorem isEquivalence_of_isReduced {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i]
    (h : Set.range (AlgebraicStack.Points.map i) = Set.univ) :
    (toBasedFunctor i).IsEquivalence :=
  sorry

/-- A closed immersion into a reduced algebraic stack whose range on points is
the whole space has the same essential image as the identity. -/
theorem essImage_eq_of_isReduced {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i]
    (h : Set.range (AlgebraicStack.Points.map i) = Set.univ) :
    (toFunctor i).essImage = (toFunctor (𝟙 X)).essImage :=
  by
    letI : (toBasedFunctor i).IsEquivalence := isEquivalence_of_isReduced i h
    let e := (toBasedFunctor i).asQuasiInverse
    letI : (toFunctor i).IsEquivalence :=
      Functor.IsEquivalence.mk' e.inverse.toFunctor
        (BasedNatIso.toNatIso e.unitIso) (BasedNatIso.toNatIso e.counitIso)
    ext K
    constructor
    · intro _
      simpa using (Functor.obj_mem_essImage (𝟭 X.total) K)
    · intro _
      exact Functor.EssSurj.mem_essImage (toFunctor i) K

/-- A closed immersion into a reduced algebraic stack is an equivalence over
the base if and only if its range on points is the whole space. -/
theorem isEquivalence_iff_range_eq_univ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i] :
    (toBasedFunctor i).IsEquivalence ↔
      Set.range (AlgebraicStack.Points.map i) = Set.univ :=
  by
    constructor
    · intro hi
      letI : (toBasedFunctor i).IsEquivalence := hi
      let e := (toBasedFunctor i).asQuasiInverse
      letI : (toFunctor i).IsEquivalence :=
        Functor.IsEquivalence.mk' e.inverse.toFunctor
          (BasedNatIso.toNatIso e.unitIso) (BasedNatIso.toNatIso e.counitIso)
      have hess : (toFunctor i).essImage = (toFunctor (𝟙 X)).essImage := by
        ext K
        constructor
        · intro _
          simpa using (Functor.obj_mem_essImage (𝟭 X.total) K)
        · intro _
          exact Functor.EssSurj.mem_essImage (toFunctor i) K
      have pointsSet_congr :
          ∀ {P Q : ObjectProperty X.total}
            (hP : AlgebraicGeometry.AlgebraicStack.Substack.IsClosed X P)
            (hQ : AlgebraicGeometry.AlgebraicStack.Substack.IsClosed X Q),
            P = Q →
              AlgebraicGeometry.AlgebraicStack.Substack.pointsSet X P hP =
                AlgebraicGeometry.AlgebraicStack.Substack.pointsSet X Q hQ := by
        intro P Q hP hQ hPQ
        subst Q
        rfl
      have hpoint := pointsSet_congr
        (AlgebraicGeometry.AlgebraicStack.image_isClosed i)
        (AlgebraicGeometry.AlgebraicStack.image_isClosed (𝟙 X)) hess
      calc
        Set.range (AlgebraicGeometry.AlgebraicStack.Points.map i) =
            AlgebraicGeometry.AlgebraicStack.Substack.pointsSet X
              (toFunctor i).essImage
              (AlgebraicGeometry.AlgebraicStack.image_isClosed i) :=
          (AlgebraicGeometry.AlgebraicStack.Substack.pointsSet_essImage i).symm
        _ = AlgebraicGeometry.AlgebraicStack.Substack.pointsSet X
              (toFunctor (𝟙 X)).essImage
              (AlgebraicGeometry.AlgebraicStack.image_isClosed (𝟙 X)) := hpoint
        _ = Set.range (AlgebraicGeometry.AlgebraicStack.Points.map (𝟙 X)) :=
          AlgebraicGeometry.AlgebraicStack.Substack.pointsSet_essImage (𝟙 X)
        _ = Set.univ := Set.range_eq_univ.mpr (by
          intro x
          exact ⟨x, AlgebraicGeometry.AlgebraicStack.Points.map_id x⟩)
    · intro h
      exact isEquivalence_of_isReduced i h

/-- A surjective closed immersion into a reduced algebraic stack is an
equivalence over the base. -/
instance isEquivalence_of_surjective_of_isReduced {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack.IsReduced X] (i : Y ⟶ X) [ClosedImmersion i] [Surjective i] :
    (toBasedFunctor i).IsEquivalence :=
  isEquivalence_of_isReduced i
    (Set.range_eq_univ.mpr (Surjective.map_surjective i))

end AlgebraicGeometry.Groupoids.Hom.ClosedImmersion
