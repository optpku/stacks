module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_17_8_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat inverse images of scheme-theoretically dense quasi-compact opens

The inverse image of a scheme-theoretically dense quasi-compact open immersion
of algebraic spaces along a flat morphism is again scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.11: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S`. Let `ι : V ⟶ Y` be a quasi-compact open immersion.
If `V` is scheme-theoretically dense in `Y`, then `openInverseImageι f ι` is
scheme-theoretically dense in `X`. -/
@[stacks 089D]
instance IsSchemeTheoreticallyDominant.openInverseImageι {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (ι : V ⟶ Y)
    [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι] :
    IsSchemeTheoreticallyDominant (openInverseImageι f ι) :=
  sorry

/-- Scheme-theoretic dominance of a quasi-compact open immersion is preserved by
pullback along a flat morphism of algebraic spaces. -/
theorem IsSchemeTheoreticallyDominant.of_isPullback {S : Scheme.{u}}
    {X Y V P : AlgebraicSpace S} {f : X ⟶ Y} {ι : V ⟶ Y} {pX : P ⟶ X}
    {pV : P ⟶ V} (h : IsPullback pX pV f ι) [Flat f] [IsOpenImmersion ι]
    [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι] :
    IsSchemeTheoreticallyDominant pX :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
