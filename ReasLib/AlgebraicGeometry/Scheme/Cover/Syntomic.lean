module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Syntomic covering families of schemes

This leaf provides both indexed syntomic covering families over a fixed scheme
and the `Scheme.Cover` presentation used by site constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- The map on points induced by an indexed family of schemes over `T`. -/
abbrev syntomicCoveringPointMap (family : ι → Over T) : (Σ i, (family i).left) → T :=
  fun p ↦ (family p.1).hom.base p.2

/-- The point map of an indexed family evaluates through the corresponding
structure morphism. -/
@[simp]
theorem syntomicCoveringPointMap_apply
    (family : ι → Over T) (p : Σ i, (family i).left) :
    syntomicCoveringPointMap family p = (family p.1).hom.base p.2 := sorry

/-- An indexed family over `T` is syntomically covering when its arrows form a
covering family for the canonical syntomic precoverage. -/
abbrev SyntomicCovering (family : ι → Over T) : Prop :=
  IsCovering (Scheme.precoverage @Syntomic)
    (ofArrows (fun i ↦ (family i).left) fun i ↦ (family i).hom)

/-- An indexed family is syntomically covering exactly when its arrows generate
a covering presieve for the canonical syntomic precoverage. -/
theorem syntomicCovering_iff_mem_precoverage (family : ι → Over T) :
    SyntomicCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        (Scheme.precoverage @Syntomic).coverings T := sorry

/-- The pointwise form of a syntomic covering: its members are syntomic and
their induced point map is surjective. -/
theorem syntomicCovering_iff (family : ι → Over T) :
    SyntomicCovering family ↔
      (∀ i : ι, Syntomic (family i).hom) ∧
        Function.Surjective (syntomicCoveringPointMap family) := sorry

/-- A syntomic covering supplies its memberwise syntomicity and joint
surjectivity. -/
theorem SyntomicCovering.source_spec {family : ι → Over T} (h : SyntomicCovering family) :
    (∀ i : ι, Syntomic (family i).hom) ∧
      Function.Surjective (syntomicCoveringPointMap family) := sorry

/-- The raw indexed-family predicate agrees with the fixed-target family
covering predicate. -/
theorem syntomicCovering_obj_iff_isCovering
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over T) :
    SyntomicCovering 𝒰.obj ↔
      CategoryTheory.SemiRepresentableFamily.Over.IsCovering
        (Scheme.precoverage @Syntomic) 𝒰 := sorry

/-- Each member of a syntomic covering family is syntomic. -/
theorem SyntomicCovering.syntomic {family : ι → Over T} (h : SyntomicCovering family) (i : ι) :
    Syntomic (family i).hom := sorry

/-- The point map of a syntomic covering family is surjective. -/
theorem SyntomicCovering.surjective_pointMap {family : ι → Over T}
    (h : SyntomicCovering family) :
    Function.Surjective (syntomicCoveringPointMap family) := sorry

/-- Every point of the target has a preimage in a syntomic covering family. -/
theorem SyntomicCovering.exists_preimage
    {family : ι → Over T} (h : SyntomicCovering family) (x : T) :
    ∃ p : Σ i, (family i).left, syntomicCoveringPointMap family p = x := sorry

/-- The arrows of a syntomic covering family generate a covering presieve in
the canonical syntomic precoverage. -/
theorem SyntomicCovering.mem_syntomic_precoverage {family : ι → Over T}
    (h : SyntomicCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      (precoverage @Syntomic).coverings T := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable (T : Scheme.{u})

namespace SyntomicCover

/-- A syntomic cover has syntomic members and jointly covers the target. -/
theorem source_spec (𝒰 : SyntomicCover T) :
    (∀ i : 𝒰.I₀, Syntomic (𝒰.f i)) ∧
      (∀ t : T, ∃ i : 𝒰.I₀, t ∈ Set.range (𝒰.f i)) := sorry

/-- Each morphism in a syntomic covering family is syntomic. -/
theorem syntomic (𝒰 : SyntomicCover T) (i : 𝒰.I₀) :
    Syntomic (𝒰.f i) := sorry

/-- The images of a syntomic covering family cover every point of its target. -/
theorem cover (𝒰 : SyntomicCover T) (t : T) :
    ∃ i : 𝒰.I₀, t ∈ Set.range (𝒰.f i) := sorry

/-- The arrows of a syntomic cover generate a covering presieve in the
canonical syntomic precoverage. -/
theorem mem_syntomic_precoverage (𝒰 : SyntomicCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ (Scheme.precoverage (@Syntomic)).coverings T := sorry

end SyntomicCover

end AlgebraicGeometry
