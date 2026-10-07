module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Smooth covering families of algebraic spaces

A smooth covering of an algebraic space is an indexed family of smooth morphisms
that is jointly surjective on points.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}

/-- The map on points induced by an indexed family of algebraic spaces over `X`. -/
def smoothCoveringPointMap (family : ι → Over X) :
    (Σ i, Points (family i).left) → Points X :=
  fun p ↦ Points.map (family p.1).hom p.2

/-- The point map of an indexed family evaluates by the induced map of the corresponding
structure morphism. -/
@[simp] theorem smoothCoveringPointMap_apply
    (family : ι → Over X) (p : Σ i, Points (family i).left) :
    smoothCoveringPointMap family p = Points.map (family p.1).hom p.2 :=
  sorry

/-- A smooth covering of `X` is an indexed family of morphisms of algebraic spaces over
`S` that are memberwise smooth and jointly surjective on points. -/
structure SmoothCovering (family : ι → Over X) : Prop where
  /-- Each member of the family is a smooth morphism of algebraic spaces over `S`. -/
  smooth : ∀ i, Smooth (family i).hom
  /-- The induced map on points is jointly surjective. -/
  surjective_pointMap : Function.Surjective (smoothCoveringPointMap family)

namespace SmoothCovering

/-- Build a smooth covering from memberwise smoothness and a surjective total point map. -/
def of (family : ι → Over X) (h_smooth : ∀ i, Smooth (family i).hom)
    (h_surj : Function.Surjective (smoothCoveringPointMap family)) :
    SmoothCovering family where
  smooth := h_smooth
  surjective_pointMap := h_surj

/-- Build a smooth covering from an unbundled family `{f_i : X_i ⟶ X}` that is memberwise
smooth and whose images of points cover `|X|`. -/
def ofFamily (Xs : ι → AlgebraicSpace S) (f : ∀ i, Xs i ⟶ X)
    (h_smooth : ∀ i, Smooth (f i))
    (h_covers : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    SmoothCovering (fun i ↦ Over.mk (f i)) where
  smooth := h_smooth
  surjective_pointMap := sorry

/-- A smooth covering consists of smooth members whose total point map is surjective. -/
theorem spec {family : ι → Over X} (h : SmoothCovering family) :
    (∀ i, Smooth (family i).hom) ∧
      Function.Surjective (smoothCoveringPointMap family) :=
  sorry

/-- A smooth covering is a memberwise smooth family whose images of points cover `|X|`. -/
theorem covers_union (family : ι → Over X) :
    SmoothCovering family ↔
      (∀ i, Smooth (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ :=
  sorry

/-- Every point of `|X|` has a preimage under the total point map of a smooth covering. -/
theorem exists_preimage {family : ι → Over X} (h : SmoothCovering family) (x : Points X) :
    ∃ p, smoothCoveringPointMap family p = x :=
  sorry

end SmoothCovering

/-- The pointwise characterization of a smooth covering: memberwise smoothness and joint
surjectivity. -/
theorem smoothCovering_iff (family : ι → Over X) :
    SmoothCovering family ↔
      (∀ i, Smooth (family i).hom) ∧
        Function.Surjective (smoothCoveringPointMap family) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

