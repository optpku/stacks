/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Proper
import StacksCheckRecall

/-!
# Scheme-theoretic images of proper morphisms of algebraic spaces

In a commutative triangle of algebraic spaces over a scheme, if the first
leg is proper and the second is separated and locally of finite type, then
the scheme-theoretic image is proper over the base and the comparison from
the source is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.40.8 (1): Let `S` be a scheme, and let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. If `f` is proper and `g` is separated and locally of finite type, then
the scheme-theoretic image of `h` is proper over `B`. -/
@[stacks 0AGD]
#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.proper_comp :
    ∀ {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι], Proper (ι ≫ g))

/- Lemma 67.40.8 (2): Let `S` be a scheme, and let `h : X ⟶ Y`, `f : X ⟶ B`,
`g : Y ⟶ B` be a commutative triangle of morphisms of algebraic spaces over
`S`. If `f` is proper and `g` is separated and locally of finite type, then
the comparison from `X` to the scheme-theoretic image of `h` is surjective. -/
@[stacks 0AGD]
#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.surjective_toImage :
    ∀ {S : Scheme.{u}} {X Y B Z : AlgebraicSpace S}
    (h : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ B) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (hcomm : h ≫ g = f) [Proper f] [Separated g] [LocallyOfFiniteType g]
    [IsSchemeTheoreticImage h toImage ι], Surjective toImage)
