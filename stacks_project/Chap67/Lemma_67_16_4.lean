/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Reduced
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 67.16.4 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `X` is reduced. Then the scheme-theoretic
image `Z` of `f` is the reduced induced algebraic space structure on the
closure of `|f|(|X|)`. -/
@[stacks 0830] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.iff_isReduced_range_eq_rangeClosure :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [AlgebraicGeometry.AlgebraicSpace.IsReduced X]
      (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι ↔
        toImage ≫ ι = f ∧ AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion ι ∧
          AlgebraicGeometry.AlgebraicSpace.IsReduced Z ∧
            Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map ι) =
              AlgebraicGeometry.AlgebraicSpace.rangeClosure f)

/- Lemma 67.16.4 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` with scheme-theoretic image `Z`. Assume `X` is
reduced. For any étale morphism `φ : V ⟶ Y`, the scheme-theoretic image of
`X ×_Y V ⟶ V` is `Z ×_Y V`. -/
@[stacks 0830] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_inverseImage_etale :
    ∀ {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z)
      (ι : Z ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.IsReduced X]
      [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι]
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion ι] (φ : V ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Etale φ] [HasPullback f φ],
      AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage (pullback.snd f φ)
        (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.pullbackToInverseImage
          f toImage ι φ)
        (AlgebraicGeometry.AlgebraicSpace.inverseImageι φ ι))
