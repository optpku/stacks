module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Factorization

/-! # Existence and uniqueness of reduced closed subspaces -/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- Any two reduced closed subspaces of an algebraic space with the same underlying point-set
admit a unique morphism over the ambient space. -/
theorem unique {S : Scheme.{u}} {X : AlgebraicSpace S} {Z Z' : ClosedSubspace X}
    (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X)
    (hZ' : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X) :
    ∃! f : Z.X ⟶ Z'.X, f ≫ Z'.ι = Z.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Construction
variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))
/-- Étale-local reducedness of the specified space with its explicit reduced atlas. -/
theorem actual_reduced :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
      (ReducedClosed.Immersion.closedSubspace X Z).X :=
  ⟨ReducedClosed.AtlasImage.reducedAtlas X Z, ReducedClosed.Space.chart X Z,
    ReducedClosed.Space.atlas_etale X Z,
    ReducedClosed.Space.atlas_surjective X Z,
    ReducedClosed.Space.reducedAtlas_reduced X Z⟩

/-- Every reduced closed subspace with the prescribed support has a unique morphism over the
ambient space to the canonical reduced closed subspace. -/
theorem actual_unique (W : ClosedSubspace X)
    (hs : W.pointsSet = (Z : Set (Points X)))
    (hr : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W.X) :
    ∃! a : W.X ⟶ (ReducedClosed.Immersion.closedSubspace X Z).X,
      a ≫ (ReducedClosed.Immersion.closedSubspace X Z).ι = W.ι := by
  sorry

/-- Every closed subset has a reduced closed subspace structure, unique up to unique
isomorphism over the ambient space. -/
theorem exists_reduced :
    ∃ W : ClosedSubspace X,
      W.pointsSet = (Z : Set (Points X)) ∧
        hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W.X ∧
          ∀ W' : ClosedSubspace X, W'.pointsSet = (Z : Set (Points X)) →
            hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W'.X →
              ∃! e : W'.X ≅ W.X, e.hom ≫ W.ι = W'.ι := by
  refine ⟨ReducedClosed.Immersion.closedSubspace X Z,
    ReducedClosed.Immersion.pointsSet_eq X Z, actual_reduced X Z, ?_⟩
  intro W' hs hr
  let W0 := ReducedClosed.Immersion.closedSubspace X Z
  have hW0 :
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) W0.X :=
    actual_reduced X Z
  have hW0_points : W0.pointsSet = (Z : Set (Points X)) :=
    ReducedClosed.Immersion.pointsSet_eq X Z
  obtain ⟨f, hf, hfu⟩ := actual_unique X Z W' hs hr
  obtain ⟨g, hg, _⟩ :=
    AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.unique
      (hW0_points.trans hs.symm) hW0 hr
  let e : W'.X ≅ W0.X :=
    { hom := f
      inv := g
      hom_inv_id := by
        obtain ⟨cancel⟩ := (ClosedSubspace.spec W').2
        apply cancel
        calc
          (f ≫ g) ≫ W'.ι = f ≫ (g ≫ W'.ι) := Category.assoc _ _ _
          _ = f ≫ W0.ι := by rw [hg]
          _ = W'.ι := hf
          _ = (𝟙 W'.X) ≫ W'.ι := by simp
      inv_hom_id := by
        obtain ⟨cancel⟩ := (ClosedSubspace.spec W0).2
        apply cancel
        calc
          (g ≫ f) ≫ W0.ι = g ≫ (f ≫ W0.ι) := Category.assoc _ _ _
          _ = g ≫ W'.ι := by rw [hf]
          _ = W0.ι := hg
          _ = (𝟙 W0.X) ≫ W0.ι := by simp }
  refine ⟨e, ?_, ?_⟩
  · change f ≫ W0.ι = W'.ι
    exact hf
  · intro e' he'
    apply Iso.ext
    exact hfu e'.hom he'


end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Construction
