/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import stacks_project.Chap99.Situation_99_16_3

/-!
# Lemma 99.16.11

In Situation 99.16.3, if `B = S` is locally Noetherian, then strong formal
effectiveness in the sense of Artin's Axioms, Remark 98.20.2 holds for
`p : Complexes f ⥤ Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- Lemma 99.16.11: in Situation 99.16.3, if `B = S` is locally Noetherian,
then every compatible system of objects of `Complexes f` over spectra of a
sequential inverse system of algebras with surjective locally nilpotent
transitions is effective over the spectrum of the inverse limit. -/
@[stacks 0DLM]
theorem strongFormalEffectiveness {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [Proper f] [Flat f] [FinitePresentation f]
    (ξ : FormalObjectSystem (p f)) :
    ξ.IsEffective := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
