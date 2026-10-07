module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Stability
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Lemma 61.12.4 (1): an isomorphism gives a singleton pro-étale covering. -/
@[stacks 098C]
#check (AlgebraicGeometry.Scheme.Proetale.cover_singleton_of_isIso :
  ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [IsIso f],
    Presieve.ofArrows (fun _ : Unit ↦ T') (fun _ ↦ f) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T)

/- Lemma 61.12.4 (2): indexed composition preserves pro-étale coverings. -/
@[stacks 098C]
#check (AlgebraicGeometry.Scheme.Proetale.cover_comp :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {κ : ι → Type w}
    (X : ι → CategoryTheory.Over T)
    (Y : (i : ι) → κ i → CategoryTheory.Over (X i).left)
    (hX : Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T)
    (hY : ∀ i : ι,
      Presieve.ofArrows (fun j ↦ (Y i j).left) (fun j ↦ (Y i j).hom) ∈
        AlgebraicGeometry.Scheme.proetalePrecoverage.coverings (X i).left),
    Presieve.ofArrows (fun p : Sigma κ ↦ (Y p.1 p.2).left)
      (fun p ↦ (Y p.1 p.2).hom ≫ (X p.1).hom) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T)

/- Lemma 61.12.4 (3): pullback preserves pro-étale coverings. -/
@[stacks 098C]
#check (AlgebraicGeometry.Scheme.Proetale.cover_pullback :
  ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    (X : ι → CategoryTheory.Over T)
    (hX : Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T) (f : T' ⟶ T),
    Presieve.ofArrows (fun i : ι ↦ pullback (X i).hom f)
      (fun i ↦ pullback.snd (X i).hom f) ∈
      AlgebraicGeometry.Scheme.proetalePrecoverage.coverings T')
