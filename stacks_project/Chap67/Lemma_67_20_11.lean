/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Diagonal
import StacksCheckRecall

/-!
# Affine permanence for morphisms of algebraic spaces

An affine composite of algebraic spaces may be cancelled when the second map
has affine or separated relative diagonal. In particular, morphisms from
affine schemes into spaces with affine absolute diagonal, or into absolutely
separated spaces, are affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

/- Lemma 67.20.11 (1): if `g : X ⟶ Y` is a morphism of algebraic spaces over
`B`, `X` is affine over `B`, and the relative diagonal
`pullback.diagonal f : Y ⟶ pullback f f` is affine, then `g` is affine. -/
@[stacks 08GB]
#check (AlgebraicGeometry.AlgebraicSpace.Affine.of_comp_of_affineDiagonal :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (g : X ⟶ Y) (f : Y ⟶ B), [Affine (g ≫ f)] → [Affine (pullback.diagonal f)] →
    Affine g)

/- Lemma 67.20.11 (2): if `g : X ⟶ Y` is a morphism of algebraic spaces over
`B`, `X` is affine over `B`, and `Y` is separated over `B`, then `g` is
affine. -/
@[stacks 08GB]
#check (AlgebraicGeometry.AlgebraicSpace.Affine.of_comp :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (g : X ⟶ Y) (f : Y ⟶ B),
    [Affine (g ≫ f)] → [Separated f] → Affine g)

/- Lemma 67.20.11 (3): a morphism from an affine scheme, viewed as an affine
algebraic space, to an algebraic space with affine diagonal over `⊤_ Scheme`
in the sense of `extendBaseTerminal` from Definition 66.3.1 is affine. -/
@[stacks 08GB]
#check (AlgebraicGeometry.AlgebraicSpace.Affine.of_isAffine_of_affineDiagonal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y), [IsAffine X] →
    [Affine (prod.lift (𝟙 (extendBaseTerminal Y)) (𝟙 (extendBaseTerminal Y)))] →
    Affine g)

/- Lemma 67.20.11 (4): a morphism from an affine scheme, viewed as an affine
algebraic space, to an absolutely separated algebraic space is affine. -/
@[stacks 08GB]
#check (AlgebraicGeometry.AlgebraicSpace.Affine.of_isAffine_of_isAbsolutelySeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y),
    [IsAffine X] → [IsAbsolutelySeparated Y] → Affine g)

end Affine

end AlgebraicGeometry.AlgebraicSpace
