module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Syntomic covering families of algebraic spaces

A syntomic covering of an algebraic space is an indexed family of syntomic
morphisms that is jointly surjective on points.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}

/-- The map on points induced by an indexed family of algebraic spaces over `X`. -/
def syntomicCoveringPointMap (family : ι → Over X) :
    (Σ i, Points (family i).left) → Points X :=
  fun p ↦ Points.map (family p.1).hom p.2

/-- The point map of an indexed family evaluates by the induced map of the corresponding
structure morphism. -/
@[simp] theorem syntomicCoveringPointMap_apply
    (family : ι → Over X) (p : Σ i, Points (family i).left) :
    syntomicCoveringPointMap family p = Points.map (family p.1).hom p.2 :=
  sorry

/-- A syntomic covering of `X` is an indexed family of morphisms of algebraic spaces over
`S` that are memberwise syntomic and jointly surjective on points. -/
structure SyntomicCovering (family : ι → Over X) : Prop where
  /-- Each member of the family is a syntomic morphism of algebraic spaces over `S`. -/
  syntomic : ∀ i, Syntomic (family i).hom
  /-- The induced map on points is jointly surjective. -/
  surjective_pointMap : Function.Surjective (syntomicCoveringPointMap family)

namespace SyntomicCovering

/-- Build a syntomic covering from memberwise syntomicity and a surjective total point map. -/
def of (family : ι → Over X) (h_syntomic : ∀ i, Syntomic (family i).hom)
    (h_surj : Function.Surjective (syntomicCoveringPointMap family)) :
    SyntomicCovering family where
  syntomic := h_syntomic
  surjective_pointMap := h_surj

/-- Build a syntomic covering from an unbundled family `{f_i : X_i ⟶ X}` that is memberwise
syntomic and whose images of points cover `|X|`. -/
def ofFamily (Xs : ι → AlgebraicSpace S) (f : ∀ i, Xs i ⟶ X)
    (h_syntomic : ∀ i, Syntomic (f i))
    (h_covers : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    SyntomicCovering (fun i ↦ Over.mk (f i)) where
  syntomic := h_syntomic
  surjective_pointMap := sorry

/-- A syntomic covering consists of syntomic members whose total point map is surjective. -/
theorem spec {family : ι → Over X} (h : SyntomicCovering family) :
    (∀ i, Syntomic (family i).hom) ∧
      Function.Surjective (syntomicCoveringPointMap family) :=
  sorry

/-- A syntomic covering is a memberwise syntomic family whose images of points cover `|X|`. -/
theorem covers_union (family : ι → Over X) :
    SyntomicCovering family ↔
      (∀ i, Syntomic (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ :=
  sorry

/-- Every point of `|X|` has a preimage under the total point map of a syntomic covering. -/
theorem exists_preimage {family : ι → Over X} (h : SyntomicCovering family) (x : Points X) :
    ∃ p, syntomicCoveringPointMap family p = x :=
  sorry

end SyntomicCovering

/-- The pointwise characterization of a syntomic covering: memberwise syntomicity and joint
surjectivity. -/
theorem syntomicCovering_iff (family : ι → Over X) :
    SyntomicCovering family ↔
      (∀ i, Syntomic (family i).hom) ∧
        Function.Surjective (syntomicCoveringPointMap family) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
