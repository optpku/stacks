/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Descent of quasi-compact morphisms of algebraic stacks along fppf algebraic-space coverings

Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of its base change along a surjective, flat, locally of
finite presentation morphism from an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Lemma 101.7.10: Let `f : X ⟶ Y` be a morphism of algebraic stacks, and let
`g : W.toGroupoids ⟶ Y` be a `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`,
and `Groupoids.Hom.LocallyOfFinitePresentation` morphism from an algebraic
space `W`. If the base change `TwoFibreProduct.snd f g` is quasi-compact, then
`f` is quasi-compact. -/
@[stacks 0DTL]
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [QuasiCompact (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    QuasiCompact f :=
  sorry

/-- Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of the second projection of a bilimit `PseudoPullbackCone`
against a surjective, flat, locally of finite presentation morphism from an
algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiCompact c.snd] :
    QuasiCompact f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
