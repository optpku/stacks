module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity.Flat
import StacksCheckRecall

/-!
# Flat inverse images of scheme-theoretically dense quasi-compact opens

The inverse image of a scheme-theoretically dense quasi-compact open immersion
of algebraic spaces along a flat morphism is again scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.11: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S`. Let `ι : V ⟶ Y` be a quasi-compact open immersion.
If `V` is scheme-theoretically dense in `Y`, then `openInverseImageι f ι` is
scheme-theoretically dense in `X`. -/
@[stacks 089D]
#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDominant.openInverseImageι :
  ∀ {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (ι : V ⟶ Y)
    [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι],
    IsSchemeTheoreticallyDominant (openInverseImageι f ι))

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDominant.of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y V P : AlgebraicSpace S} {f : X ⟶ Y} {ι : V ⟶ Y} {pX : P ⟶ X}
    {pV : P ⟶ V} (h : IsPullback pX pV f ι) [Flat f] [IsOpenImmersion ι]
    [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι],
    IsSchemeTheoreticallyDominant pX)

end AlgebraicGeometry.AlgebraicSpace
