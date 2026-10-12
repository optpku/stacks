/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Recognition criteria for pro-étale covering families
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

variable {T : Scheme.{u}} {ι : Type v}

/-- A family over a scheme is pro-étale covering exactly when its canonical
presieve is fpqc covering and each member is weakly étale. -/
theorem cover_iff_fpqc (X : ι → Over T) :
    Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
        Scheme.proetalePrecoverage.coverings T ↔
      (∀ i : ι, WeaklyEtale (X i).hom) ∧
        Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
          Scheme.fpqcPrecoverage.coverings T := sorry

/-- A family over a scheme is pro-étale covering exactly when its members are
weakly étale and compact-open cover every affine open of the target. -/
theorem cover_iff_affine (X : ι → Over T) :
    Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
        Scheme.proetalePrecoverage.coverings T ↔
      (∀ i : ι, WeaklyEtale (X i).hom) ∧
        ∀ U : T.Opens, IsAffineOpen U →
          IsCompactOpenCovered (fun i ↦ (X i).hom) (U : Set T) := sorry

/-- A family over a scheme is pro-étale covering exactly when its members are
weakly étale and compact-open cover the members of an affine open cover. -/
theorem cover_iff_refinement (X : ι → Over T) :
    Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
        Scheme.proetalePrecoverage.coverings T ↔
      (∀ i : ι, WeaklyEtale (X i).hom) ∧
        ∃ 𝒰 : Scheme.AffineOpenCover.{u} T,
          ∀ a : 𝒰.I₀,
            IsCompactOpenCovered (fun i ↦ (X i).hom)
              ((𝒰.f a).opensRange : Set T) := sorry

/-- For a quasi-separated target, a family is pro-étale covering exactly when
its members are weakly étale and compact-open cover a neighborhood of every
point. -/
theorem cover_iff_neighborhood (X : ι → Over T) [QuasiSeparatedSpace T] :
    Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
        Scheme.proetalePrecoverage.coverings T ↔
      (∀ i : ι, WeaklyEtale (X i).hom) ∧
        ∀ t : T, ∃ K : Set T,
          IsCompactOpenCovered (fun i ↦ (X i).hom) K ∧ K ∈ nhds t := sorry

end AlgebraicGeometry.Scheme.Proetale
