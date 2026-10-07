module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth covering families of schemes

This leaf defines smooth covering families through the canonical smooth
precoverage and retains the pointwise form needed by geometric arguments.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- The map on points induced by an indexed family of schemes over `T`. -/
abbrev smoothCoveringPointMap (family : ι → Over T) : (Σ i, (family i).left) → T :=
  fun p ↦ (family p.1).hom.base p.2

/-- The point map of an indexed family evaluates by its corresponding structure morphism. -/
@[simp] theorem smoothCoveringPointMap_apply
    (family : ι → Over T) (p : Σ i, (family i).left) :
    smoothCoveringPointMap family p = (family p.1).hom.base p.2 := rfl

/-- A smooth covering of `T` is an indexed family in the canonical smooth precoverage. -/
@[stacks 021Z]
abbrev SmoothCovering (family : ι → Over T) : Prop :=
  Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
    (Scheme.precoverage @Smooth).coverings T

/-- A smooth covering is precisely a covering presieve for the canonical smooth precoverage. -/
theorem smoothCovering_iff_mem_precoverage (family : ι → Over T) :
    SmoothCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        (Scheme.precoverage @Smooth).coverings T := sorry

/-- The pointwise characterization of a smooth covering: memberwise smoothness and joint
surjectivity. -/
theorem smoothCovering_iff (family : ι → Over T) :
    SmoothCovering family ↔
      (∀ i : ι, Smooth (family i).hom) ∧
        Function.Surjective (smoothCoveringPointMap family) := sorry

/-- A smooth covering consists of smooth members whose total point map is surjective. -/
theorem SmoothCovering.source_spec {family : ι → Over T} (h : SmoothCovering family) :
    (∀ i : ι, Smooth (family i).hom) ∧
      Function.Surjective (smoothCoveringPointMap family) := sorry

/-- Every member of a smooth covering family is smooth. -/
theorem SmoothCovering.smooth {family : ι → Over T} (h : SmoothCovering family) (i : ι) :
    Smooth (family i).hom := sorry

/-- The point map of a smooth covering family is surjective. -/
theorem SmoothCovering.surjective_pointMap {family : ι → Over T} (h : SmoothCovering family) :
    Function.Surjective (smoothCoveringPointMap family) := sorry

/-- Every point of the target has a preimage in a smooth covering family. -/
theorem SmoothCovering.exists_preimage
    {family : ι → Over T} (h : SmoothCovering family) (x : T) :
    ∃ p : Σ i, (family i).left, smoothCoveringPointMap family p = x := sorry

/-- The arrows of a smooth covering family generate a covering presieve in the smooth
precoverage. -/
theorem SmoothCovering.mem_smooth_precoverage {family : ι → Over T} (h : SmoothCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      (precoverage @Smooth).coverings T := sorry

end AlgebraicGeometry.Scheme
