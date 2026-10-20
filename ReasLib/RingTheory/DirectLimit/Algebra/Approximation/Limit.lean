module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limit computations for directed algebra approximations

This leaf owns the bundled and pointwise formulas for the canonical maps from
approximation stages to the two limiting rings, together with their scalar
tower and stage-map naturality properties.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- The source stage map evaluates through the chosen source colimit equivalence. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem sourceToLimit_apply (A : Hom f) (i : A.index) (x : A.source i) :
    A.sourceToLimit i x =
      A.sourceColimit (Ring.DirectLimit.of A.source
        (fun i j h ↦ A.sourceMap i j h) i x) := sorry

/-- The target stage map evaluates through the chosen target colimit equivalence. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem targetToLimit_apply (A : Hom f) (i : A.index) (x : A.target i) :
    A.targetToLimit i x =
      A.targetColimit (Ring.DirectLimit.of A.target
        (fun i j h ↦ A.targetMap i j h) i x) := sorry

/-- The canonical map from a source stage to the limiting target ring.  This
map is the stage map followed by the target direct-limit comparison. -/
@[stacks 00R0 "directed ring-hom approximation limit"]
noncomputable def mapToLimit (A : Hom f) (i : A.index) : A.source i →+* S :=
  (A.targetToLimit i).comp (A.map i)

/-- The canonical maps from source stages to the limiting source ring respect
the source transition maps. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem sourceToLimit_comp_sourceMap (A : Hom f) {i j : A.index} (h : i ≤ j) :
    (A.sourceToLimit j).comp (A.sourceMap i j h) = A.sourceToLimit i := sorry

/-- The source stage maps commute pointwise with source transitions. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem sourceToLimit_sourceMap_apply (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.source i) :
    A.sourceToLimit j (A.sourceMap i j h x) = A.sourceToLimit i x := sorry

/-- The canonical maps from target stages to the limiting target ring respect
the target transition maps. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem targetToLimit_comp_targetMap (A : Hom f) {i j : A.index} (h : i ≤ j) :
    (A.targetToLimit j).comp (A.targetMap i j h) = A.targetToLimit i := sorry

/-- The target stage maps commute pointwise with target transitions. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem targetToLimit_targetMap_apply (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.target i) :
    A.targetToLimit j (A.targetMap i j h x) = A.targetToLimit i x := sorry

/-- The stagewise approximation map commutes with both transition systems in
pointwise form. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem map_comp_sourceMap_apply (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.source i) :
    A.map j (A.sourceMap i j h x) = A.targetMap i j h (A.map i x) := sorry

/-- The stagewise approximation maps commute with source and target
transitions as an equality of ring homomorphisms.  This bundled form is the
naturality square needed when composing further direct-limit maps. -/
@[stacks 00R0 "directed ring-hom approximation limit"]
theorem map_comp_sourceMap (A : Hom f) {i j : A.index} (h : i ≤ j) :
    (A.map j).comp (A.sourceMap i j h) =
      (A.targetMap i j h).comp (A.map i) := A.map_comm h

/-- The source transition and the two maps from comparable source stages to
the limiting source ring form a scalar tower. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem sourceToLimit_tower (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra (A.source j) R := (A.sourceToLimit j).toAlgebra
    IsScalarTower (A.source i) (A.source j) R := sorry

/-- The target transition and the two maps from comparable target stages to
the limiting target ring form a scalar tower. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem targetToLimit_tower (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j h).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : Algebra (A.target j) S := (A.targetToLimit j).toAlgebra
    IsScalarTower (A.target i) (A.target j) S := sorry

/-- Comparable source stages carry the canonical scalar tower induced by their
transition homomorphisms. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem sourceMap_isScalarTower (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) :
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j hij).toAlgebra
    let _ : Algebra (A.source i) (A.source k) :=
      (A.sourceMap i k (hij.trans hjk)).toAlgebra
    let _ : Algebra (A.source j) (A.source k) := (A.sourceMap j k hjk).toAlgebra
    IsScalarTower (A.source i) (A.source j) (A.source k) := sorry

/-- Comparable target stages carry the canonical scalar tower induced by their
transition homomorphisms. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem targetMap_isScalarTower (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) :
    let _ : Algebra (A.target i) (A.target j) := (A.targetMap i j hij).toAlgebra
    let _ : Algebra (A.target i) (A.target k) :=
      (A.targetMap i k (hij.trans hjk)).toAlgebra
    let _ : Algebra (A.target j) (A.target k) := (A.targetMap j k hjk).toAlgebra
    IsScalarTower (A.target i) (A.target j) (A.target k) := sorry

/-- A source stage, a comparable target stage, and the limiting target ring
form a scalar tower through the stage map and the target-limit map. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem mapToLimit_tower (A : Hom f)
    {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.targetMap i j h).comp (A.map i)).toAlgebra
    let _ : Algebra (A.target j) S := (A.targetToLimit j).toAlgebra
    let _ : Algebra (A.source i) S := (A.mapToLimit i).toAlgebra
    IsScalarTower (A.source i) (A.target j) S := sorry

/-- The stagewise map commutes with the prescribed map after passing both
systems to their limiting rings. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem mapToLimit_commutes (A : Hom f) (i : A.index) :
    A.mapToLimit i = f.comp (A.sourceToLimit i) := sorry

/-- The stagewise map evaluates compatibly with the prescribed limiting map. -/
@[simp, stacks 00R0 "directed ring-hom approximation limit"]
theorem mapToLimit_apply (A : Hom f) (i : A.index) (x : A.source i) :
    A.mapToLimit i x = f (A.sourceToLimit i x) := sorry

/-- The target-stage map to the limiting target is compatible with the source
stage action induced by the limiting map. -/
@[stacks 00R1 "directed approximation scalar tower"]
theorem targetToLimit_isScalarTower (A : Hom f) (i : A.index) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S := (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    IsScalarTower (A.source i) (A.target i) S := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
