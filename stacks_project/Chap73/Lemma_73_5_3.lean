module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Lemma 73.5.3 (1): an isomorphism gives a singleton smooth covering. -/
@[stacks 041D] #check
  (AlgebraicGeometry.AlgebraicSpace.smoothCovering_singleton_of_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X X' : AlgebraicGeometry.AlgebraicSpace S}
      (f : X' ⟶ X) [IsIso f],
      AlgebraicGeometry.AlgebraicSpace.SmoothCovering
        (fun _ : Unit ↦ Over.mk f))

/- Lemma 73.5.3 (2): indexed composition preserves smooth coverings. -/
@[stacks 041D] #check
  (AlgebraicGeometry.AlgebraicSpace.smoothCovering_comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v} {κ : ι → Type w}
      (Xfam : ι → Over X)
      (Y : (i : ι) → κ i → Over (Xfam i).left),
      AlgebraicGeometry.AlgebraicSpace.SmoothCovering Xfam →
        (∀ i, AlgebraicGeometry.AlgebraicSpace.SmoothCovering (Y i)) →
          AlgebraicGeometry.AlgebraicSpace.SmoothCovering
            (fun p : Sigma κ ↦
              Over.mk ((Y p.1 p.2).hom ≫ (Xfam p.1).hom)))

/- Lemma 73.5.3 (3): pullback preserves smooth coverings. -/
@[stacks 041D] #check
  (AlgebraicGeometry.AlgebraicSpace.smoothCovering_pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X X' : AlgebraicGeometry.AlgebraicSpace S} {ι : Type v}
      (Xfam : ι → Over X),
      AlgebraicGeometry.AlgebraicSpace.SmoothCovering Xfam →
        (f : X' ⟶ X) →
          AlgebraicGeometry.AlgebraicSpace.SmoothCovering
            (fun i ↦ Over.mk (pullback.fst f (Xfam i).hom)))
