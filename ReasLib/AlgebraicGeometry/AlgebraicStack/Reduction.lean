/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.ClosedImmersion
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Comparison
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Fpqc
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.BaseChange
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.Fpqc
import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Equivalence
import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Reduced induced structures and reduction

The reduced object property on a closed point-set is the intersection of the
essential images of all reduced closed immersions with that range on points.
Its restricted category gives the reduced induced stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids (toFunctor)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

namespace Substack

/-- The reduced object property consists of the objects in every reduced closed
immersion with the prescribed range on points. -/
def reducedProperty (Z : Closeds (Points X)) : ObjectProperty X.total :=
  fun x => ∀ (Y : GroupoidsOver S) [AlgebraicStack Y] (i : Y ⟶ X),
    ClosedImmersion i → Set.range (Points.map i) = Z.carrier → IsReduced Y →
      (toFunctor i).essImage x

/-- The reduced object property is the essential image of every reduced closed
immersion having the prescribed range on points. -/
theorem reducedProperty_eq_essImage (Z : Closeds (Points X))
    {Y : GroupoidsOver S} [AlgebraicStack Y] (i : Y ⟶ X) [ClosedImmersion i]
    (hZ : Set.range (Points.map i) = Z.carrier) (hY : IsReduced Y) :
    reducedProperty Z = (toFunctor i).essImage := by
  funext x
  apply propext
  constructor
  · intro hx
    exact hx Y i inferInstance hZ hY
  · intro hx Y' _ j hj hjZ hjY
    letI := hj
    have h := reduced_closedImmersion_essImage_eq i j hY hjY (hZ.trans hjZ.symm)
    exact h ▸ hx

/-- The reduced object property defines a closed substack. -/
theorem reducedProperty_isClosed (Z : Closeds (Points X)) :
    IsClosed X (reducedProperty Z) := by
  obtain ⟨Y, hA, i, hI, _, _, hZ, hY, _⟩ :=
    exists_reduced_closedImmersion Z.carrier Z.isClosed
  letI := hA
  letI := hI
  rw [reducedProperty_eq_essImage Z i hZ hY]
  exact image_isClosed i

/-- The closed substack defined by the reduced object property has exactly the
prescribed point-set. -/
theorem reducedProperty_pointsSet (Z : Closeds (Points X)) :
    pointsSet X (reducedProperty Z) (reducedProperty_isClosed Z) = Z.carrier := by
  obtain ⟨Y, hA, i, hI, _, _, hZ, hY, _⟩ :=
    exists_reduced_closedImmersion Z.carrier Z.isClosed
  letI := hA
  letI := hI
  calc
    pointsSet X (reducedProperty Z) (reducedProperty_isClosed Z) =
        pointsSet X (toFunctor i).essImage (image_isClosed i) := by
      congr 1
      exact reducedProperty_eq_essImage Z i hZ hY
    _ = Set.range (Points.map i) := pointsSet_essImage i
    _ = Z.carrier := hZ

/-- The category restricted to the reduced object property is reduced. -/
instance instIsReduced_reducedCategory (Z : Closeds (Points X)) :
    IsReduced (closedCategory X (reducedProperty Z) (reducedProperty_isClosed Z)) := by
  obtain ⟨Y, hA, i, hI, _, _, hZ, hY, _⟩ :=
    exists_reduced_closedImmersion Z.carrier Z.isClosed
  letI := hA
  letI := hI
  have hred : ∀ (P : ObjectProperty X.total) (hP : IsClosed X P),
      P = (toFunctor i).essImage → IsReduced (closedCategory X P hP) := by
    intro P hP hEq
    subst P
    obtain ⟨h, j, hj, _⟩ := (existsUnique_image i).2.1
    obtain ⟨qinv⟩ := hj.nonempty
    let e : Y ≌ closedCategory X (toFunctor i).essImage hP :=
      Bicategory.Equivalence.mkOfAdjointifyCounit (f := j)
        (g := FiberedCategoryOver.Groupoids.ofBasedFunctor qinv.inverse)
        (Bicategory.InducedBicategory.isoMk qinv.unitIso)
        (Bicategory.InducedBicategory.isoMk qinv.counitIso)
    have hle : AlgebraicSpace.fppfPrecoverage S ≤ AlgebraicSpace.fpqcPrecoverage S := by
      intro F R hR
      obtain ⟨ι, Fᵢ, f, rfl⟩ := R.exists_eq_ofArrows
      exact (AlgebraicSpace.ofArrows_mem_fpqcPrecoverage_iff f).mpr
        (AlgebraicSpace.fpqcCovering_of_fppfCovering
          ((AlgebraicSpace.fppfCovering_iff_mem_precoverage Fᵢ f).mpr hR))
    letI : MorphismProperty.IsLocalAtTarget (@AlgebraicSpace.Smooth S)
        (AlgebraicSpace.fppfPrecoverage S) :=
      MorphismProperty.IsLocalAtTarget.of_le hle
    letI : MorphismProperty.IsLocalAtTarget (@AlgebraicSpace.Surjective S)
        (AlgebraicSpace.fppfPrecoverage S) :=
      MorphismProperty.IsLocalAtTarget.of_le hle
    obtain ⟨U, p, hp, hsurj, hU⟩ := hY.exists_reduced_smooth_cover
    have hrep : relativelyRepresentableByAlgebraicSpaces (p ≫ e.hom) :=
      (relativelyRepresentableByAlgebraicSpaces.iff_of_equivalence
        (Bicategory.Equivalence.id _) e (p ≫ e.hom) p (λ_ _)).mpr hp.representable
    have hsm := (Groupoids.Hom.has.iff_of_equivalence (@AlgebraicSpace.Smooth S)
      (Bicategory.Equivalence.id _) e (p ≫ e.hom) p (λ_ _) hrep).mpr hp.of_represents
    have hsur := (Groupoids.Hom.has.iff_of_equivalence (@AlgebraicSpace.Surjective S)
      (Bicategory.Equivalence.id _) e (p ≫ e.hom) p (λ_ _) hrep).mpr hsurj.of_represents
    exact ⟨U, p ≫ e.hom, ⟨hrep, hsm⟩, ⟨hrep, hsur⟩, hU⟩
  exact hred _ _ (reducedProperty_eq_essImage Z i hZ hY)

end Substack

namespace ClosedSubstackStructure

/-- The reduced induced structure on a closed point-set is its reduced object property. -/
@[reducible]
def reduced (Z : Closeds (Points X)) : ClosedSubstackStructure Z :=
  ⟨Substack.reducedProperty Z, Substack.reducedProperty_isClosed Z,
    Substack.reducedProperty_pointsSet Z⟩

/-- The reduced induced structure is reduced and has the prescribed range on points. -/
theorem reduced_spec (Z : Closeds (Points X)) :
    Set.range (Points.map (reduced Z).ι) = Z.carrier ∧ IsReduced (reduced Z).Y := by
  exact ⟨(spec (reduced Z)).2, inferInstance⟩

/-- Every reduced structure on a closed point-set has the same object property
as the reduced induced structure. -/
theorem reduced_unique {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z)
    (hT : IsReduced T.Y) : T.val = (reduced Z).val := by
  calc
    T.val = (toFunctor T.ι).essImage :=
      (Substack.closedInclusion_essImage X T.val _).symm
    _ = (reduced Z).val :=
      (Substack.reducedProperty_eq_essImage Z T.ι (spec T).2 hT).symm

end ClosedSubstackStructure

/-- The reduction of an algebraic stack is the reduced induced stack on its whole point space. -/
abbrev reduction (X : GroupoidsOver S) [AlgebraicStack X] : GroupoidsOver S :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y

/-- The reduction includes into the ambient stack by the literal closed-substack inclusion. -/
abbrev reductionι (X : GroupoidsOver S) [AlgebraicStack X] : reduction X ⟶ X :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι

/-- The reduction is reduced, and its inclusion is a closed immersion surjective on points. -/
theorem reduction_spec (X : GroupoidsOver S) [AlgebraicStack X] :
    IsReduced (reduction X) ∧ ClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)) := by
  refine ⟨(ClosedSubstackStructure.reduced_spec (⊤ : Closeds (Points X))).2,
    inferInstance, ?_⟩
  exact Set.range_eq_univ.mp
    (ClosedSubstackStructure.reduced_spec (⊤ : Closeds (Points X))).1

/-- The reduction is the underlying stack of the reduced structure on the top closed subset. -/
theorem reduction_eq_reduced_top (X : GroupoidsOver S) [AlgebraicStack X] :
    reduction X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y :=
  rfl

/-- The reduction inclusion is the inclusion of the reduced structure on the top closed subset. -/
theorem reductionι_eq_reduced_top_ι (X : GroupoidsOver S) [AlgebraicStack X] :
    reductionι X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι :=
  rfl

end AlgebraicGeometry.AlgebraicStack
