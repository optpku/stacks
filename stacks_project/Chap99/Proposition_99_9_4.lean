/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_9_1_1_Functor»
public import stacks_project.Chap99.Proposition_99_8_4_Representable

/-!
# Proposition 99.9.4

If `f : X ⟶ B` is a finitely presented separated morphism of algebraic spaces
over a scheme `S`, then the Hilbert functor `Hilb_{X/B}` is an algebraic space
locally of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- Proposition 99.9.4: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. If `f` is of finite presentation and separated, then
`hilbert f` (`Hilb_{X/B}`) is an algebraic space locally of finite presentation
over `B`. -/
@[stacks 0D01]
theorem hilbert_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    IsLocallyOfFinitePresentationOver (hilbert f) :=
  sorry

/-- If `f : X ⟶ B` is finitely presented and separated, then `hilbert f` is
represented by an algebraic space over `B`. -/
theorem hilbert_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    IsAlgebraicSpaceOver (hilbert f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
