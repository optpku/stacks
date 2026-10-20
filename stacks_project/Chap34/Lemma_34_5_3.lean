module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Lemma 34.5.3 (1): an isomorphism gives a singleton smooth covering. -/
@[stacks 0221] #check
  (AlgebraicGeometry.Scheme.smoothCovering_singleton_of_isIso :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [IsIso f],
      AlgebraicGeometry.Scheme.SmoothCovering (fun _ : Unit ↦ Over.mk f))

/- Lemma 34.5.3 (2): indexed composition preserves smooth coverings. -/
@[stacks 0221] #check
  (AlgebraicGeometry.Scheme.smoothCovering_comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {κ : ι → Type w}
      (X : ι → Over T) (Y : (i : ι) → κ i → Over (X i).left)
      (hX : AlgebraicGeometry.Scheme.SmoothCovering X)
      (hY : ∀ i : ι, AlgebraicGeometry.Scheme.SmoothCovering (Y i)),
      AlgebraicGeometry.Scheme.SmoothCovering (fun p : Sigma κ ↦
        Over.mk ((Y p.1 p.2).hom ≫ (X p.1).hom)))

/- Lemma 34.5.3 (3): base change along any scheme morphism preserves smooth coverings. -/
@[stacks 0221] #check
  (AlgebraicGeometry.Scheme.smoothCovering_pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → Over T) (hX : AlgebraicGeometry.Scheme.SmoothCovering X) (f : T' ⟶ T),
      AlgebraicGeometry.Scheme.SmoothCovering
        (fun i : ι ↦ Over.mk (pullback.fst f (X i).hom)))
