/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_12_1_Mor
public import stacks_project.Chap99.Proposition_99_9_4

/-!
# Proposition 99.12.3

If `x : X ⟶ B` is finitely presented and separated and `z : Z ⟶ B` is
finitely presented, flat, and proper, then the relative Hom functor
`Mor_B(Z, X)` is an algebraic space locally of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Proposition 99.12.3: Let `S` be a scheme. Let `z : Z ⟶ B` and `x : X ⟶ B`
be morphisms of algebraic spaces over `S`. If `x` is of finite presentation
and separated and `z` is of finite presentation, flat, and proper, then
`mor z x` (`Mor_B(Z, X)`) is an algebraic space locally of finite
presentation over `B`. -/
@[stacks 0D1C]
theorem mor_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [FinitePresentation x] [Separated x] [FinitePresentation z] [Flat z]
    [Proper z] : IsLocallyOfFinitePresentationOver (mor z x) :=
  sorry

/-- If `x : X ⟶ B` is finitely presented and separated and `z : Z ⟶ B` is
finitely presented, flat, and proper, then `mor z x` is represented by an
algebraic space over `B`. -/
theorem mor_isAlgebraicSpaceOver {S : Scheme.{u}} {Z B X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) [FinitePresentation x] [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    IsAlgebraicSpaceOver (mor z x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
