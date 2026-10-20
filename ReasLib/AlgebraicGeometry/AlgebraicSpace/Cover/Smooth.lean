module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage

/-!
# Smooth covering families of algebraic spaces

Smooth covering families are jointly surjective families of smooth morphisms,
expressed through the canonical morphism-property precoverage.
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
  rfl

/-- A smooth covering of `X` is an indexed family in the precoverage of jointly
surjective smooth morphisms of algebraic spaces over `S`. -/
abbrev SmoothCovering (family : ι → Over X) : Prop :=
  Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
    precoverage (fun {_ _} f ↦ Smooth f) X

/-- The pointwise characterization of a smooth covering: memberwise smoothness and joint
surjectivity. -/
theorem smoothCovering_iff (family : ι → Over X) :
    SmoothCovering family ↔
      (∀ i, Smooth (family i).hom) ∧
        Function.Surjective (smoothCoveringPointMap family) :=
  sorry

namespace SmoothCovering

/-- Every member of a smooth covering is a smooth morphism. -/
theorem smooth {family : ι → Over X} (h : SmoothCovering family) (i : ι) :
    Smooth (family i).hom :=
  ((smoothCovering_iff family).mp h).1 i

/-- The total point map of a smooth covering is surjective. -/
theorem surjective_pointMap {family : ι → Over X} (h : SmoothCovering family) :
    Function.Surjective (smoothCoveringPointMap family) :=
  ((smoothCovering_iff family).mp h).2

/-- A memberwise smooth family with a surjective total point map is a smooth covering. -/
def of (family : ι → Over X) (h_smooth : ∀ i, Smooth (family i).hom)
    (h_surj : Function.Surjective (smoothCoveringPointMap family)) :
    SmoothCovering family :=
  (smoothCovering_iff family).mpr ⟨h_smooth, h_surj⟩

/-- A smooth covering consists of smooth members whose total point map is surjective. -/
theorem spec {family : ι → Over X} (h : SmoothCovering family) :
    (∀ i, Smooth (family i).hom) ∧
      Function.Surjective (smoothCoveringPointMap family) :=
  (smoothCovering_iff family).mp h

/-- A smooth covering is a memberwise smooth family whose images of points cover `|X|`. -/
theorem covers_union (family : ι → Over X) :
    SmoothCovering family ↔
      (∀ i, Smooth (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ :=
  ofArrows_mem_precoverage_iff (fun {_ _} f ↦ Smooth f) (fun i ↦ (family i).hom)

/-- An unbundled memberwise smooth family whose images of points cover `|X|`
defines a smooth covering. -/
def ofFamily (Xs : ι → AlgebraicSpace S) (f : ∀ i, Xs i ⟶ X)
    (h_smooth : ∀ i, Smooth (f i))
    (h_covers : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    SmoothCovering (fun i ↦ Over.mk (f i)) :=
  (covers_union (fun i ↦ Over.mk (f i))).mpr ⟨h_smooth, h_covers⟩

/-- Every point of `|X|` has a preimage under the total point map of a smooth covering. -/
theorem exists_preimage {family : ι → Over X} (h : SmoothCovering family) (x : Points X) :
    ∃ p, smoothCoveringPointMap family p = x :=
  h.surjective_pointMap x

end SmoothCovering

end AlgebraicGeometry.AlgebraicSpace
