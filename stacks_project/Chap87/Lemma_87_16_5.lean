/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_16_5_Separated

/-!
# Lemma 87.16.5

A morphism from a separated algebraic space to a formal algebraic space is
separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Lemma 87.16.5: Let `S` be a scheme. Let `X` be a formal algebraic space over
`S`. Let `U ⟶ X` be a morphism where `U` is a separated algebraic space over
`S`. Then `U ⟶ X` is separated. -/
@[stacks 0APX]
instance instSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {U X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsSeparated U] [IsFormalAlgebraicSpace X] (f : U ⟶ X) :
    Separated f :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
