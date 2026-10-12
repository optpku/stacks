/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Lemma 87.19.6

A sheaf map into a formal algebraic space that is representable by algebraic
spaces has formal algebraic space as its domain.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- Lemma 87.19.6: Let `S` be a scheme. Let `Y` be a formal algebraic space
over `S`. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which is
representable by algebraic spaces. Then `X` is a formal algebraic space. -/
@[stacks 0AJI]
theorem of_representableByAlgebraicSpaces_of_formal
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) :
    IsFormalAlgebraicSpace X :=
  sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
