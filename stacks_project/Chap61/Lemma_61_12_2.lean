module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Criteria
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 61.12.2: an indexed family of scheme morphisms is a pro-étale covering
if and only if each map is weakly étale and the family satisfies any of the
fpqc recognition criteria. -/
@[stacks 098A] #check
  (AlgebraicGeometry.Scheme.Proetale.cover_iff_fpqc :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      CategoryTheory.Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
          AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T ↔
        (∀ i : ι, AlgebraicGeometry.WeaklyEtale (X i).hom) ∧
          CategoryTheory.Presieve.ofArrows (fun i ↦ (X i).left)
              (fun i ↦ (X i).hom) ∈
            AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings T)

#check
  (AlgebraicGeometry.Scheme.Proetale.cover_iff_affine :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      CategoryTheory.Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
          AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T ↔
        (∀ i : ι, AlgebraicGeometry.WeaklyEtale (X i).hom) ∧
          ∀ U : T.Opens, AlgebraicGeometry.IsAffineOpen U →
            IsCompactOpenCovered (fun i ↦ (X i).hom) (U : Set T))

#check
  (AlgebraicGeometry.Scheme.Proetale.cover_iff_refinement :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      CategoryTheory.Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
          AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T ↔
        (∀ i : ι, AlgebraicGeometry.WeaklyEtale (X i).hom) ∧
          ∃ 𝒰 : AlgebraicGeometry.Scheme.AffineOpenCover.{u} T,
            ∀ a : 𝒰.I₀,
              IsCompactOpenCovered (fun i ↦ (X i).hom)
                ((𝒰.f a).opensRange : Set T))

#check
  (AlgebraicGeometry.Scheme.Proetale.cover_iff_neighborhood :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T) [QuasiSeparatedSpace T],
      CategoryTheory.Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
          AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T ↔
        (∀ i : ι, AlgebraicGeometry.WeaklyEtale (X i).hom) ∧
          ∀ t : T, ∃ K : Set T,
            IsCompactOpenCovered (fun i ↦ (X i).hom) K ∧ K ∈ nhds t)
