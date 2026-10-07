module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Open immersions into scheme-theoretic images

If an immersion of algebraic spaces is quasi-compact or has reduced source,
any scheme-theoretic image factorization is an open immersion that is
scheme-theoretically and topologically dense. Competing image factorizations
remain explicit; there is no chosen `Hom.image`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticImage

/-- Lemma 67.17.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be an immersion of
algebraic spaces over `S`, written `h : Z ⟶ X` in the source. Assume either
`f` is quasi-compact or `X` is reduced. Let `toImage : X ⟶ Z` and `ι : Z ⟶ Y`
be a scheme-theoretic image factorization of `f`, so `Z` plays the role of
the scheme-theoretic image `Z̄ ⊂ Y`. Then `toImage` is an open immersion. -/
@[stacks 088G]
theorem isOpenImmersion_toImage_of_quasiCompact_or_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsSchemeTheoreticImage f toImage ι]
    (hqc_or_red : QuasiCompact f ∨ IsReduced X) :
    IsOpenImmersion toImage :=
  sorry

/-- Lemma 67.17.7 (2): under the same hypotheses, if `toImage` is an open
immersion then it is scheme-theoretically dense, so it identifies `X` with a
scheme-theoretically dense open subspace of the image `Z`. -/
@[stacks 088G]
theorem isSchemeTheoreticallyDense_toImage_of_quasiCompact_or_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsSchemeTheoreticImage f toImage ι]
    [IsOpenImmersion toImage]
    (hqc_or_red : QuasiCompact f ∨ IsReduced X) :
    IsSchemeTheoreticallyDense toImage :=
  sorry

/-- Lemma 67.17.7 (3): under the same hypotheses, `toImage` is dominant, so `X`
is topologically dense in the scheme-theoretic image `Z`. -/
@[stacks 088G]
theorem dominant_toImage_of_quasiCompact_or_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsSchemeTheoreticImage f toImage ι]
    (hqc_or_red : QuasiCompact f ∨ IsReduced X) :
    Dominant toImage :=
  sorry

/-- The comparison from a quasi-compact immersion to a scheme-theoretic image is
an open immersion. -/
theorem isOpenImmersion_toImage_of_quasiCompact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] :
    IsOpenImmersion toImage :=
  sorry

/-- The comparison from an immersion with reduced source to a scheme-theoretic
image is an open immersion. -/
theorem isOpenImmersion_toImage_of_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsReduced X] [IsSchemeTheoreticImage f toImage ι] :
    IsOpenImmersion toImage :=
  sorry

/-- The comparison from a quasi-compact immersion to a scheme-theoretic image is
scheme-theoretically dense. -/
theorem isSchemeTheoreticallyDense_toImage_of_quasiCompact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι]
    [IsOpenImmersion toImage] :
    IsSchemeTheoreticallyDense toImage :=
  sorry

/-- The comparison from an immersion with reduced source to a scheme-theoretic
image is scheme-theoretically dense. -/
theorem isSchemeTheoreticallyDense_toImage_of_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsReduced X] [IsSchemeTheoreticImage f toImage ι]
    [IsOpenImmersion toImage] :
    IsSchemeTheoreticallyDense toImage :=
  sorry

/-- The comparison from an immersion with reduced source to a scheme-theoretic
image is dominant. The quasi-compact case without an immersion hypothesis is
`dominant_toImage`. -/
theorem dominant_toImage_of_isReduced
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsImmersion f] [IsReduced X] [IsSchemeTheoreticImage f toImage ι] :
    Dominant toImage :=
  sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
