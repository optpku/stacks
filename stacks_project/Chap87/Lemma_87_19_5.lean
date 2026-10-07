module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Lemma 87.19.5

A sheaf map into an affine formal algebraic space that is representable by
algebraic spaces has formal algebraic space as its domain.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- Lemma 87.19.5: Let `S` be a scheme. Let `Y` be an affine formal algebraic
space over `S`. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable by algebraic spaces. Then `X` is a formal algebraic space. -/
@[stacks 0AJH]
theorem of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace Y] {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) :
    IsFormalAlgebraicSpace X :=
  sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
