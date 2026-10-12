/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Fibre products of formal algebraic spaces

The sheaf fibre product of formal algebraic spaces over a sheaf whose
diagonal is representable by algebraic spaces is again a formal algebraic
space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- Lemma 87.15.2: Let `S` be a scheme. Let `X`, `Y` be formal algebraic spaces
over `S` and let `Z` be a sheaf whose diagonal is representable by algebraic
spaces. Let `X ⟶ Z` and `Y ⟶ Z` be maps of sheaves. Then the sheaf fibre
product `pullback f g` is a formal algebraic space. -/
@[stacks 0AJ2]
theorem ofPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h_diag : representableByAlgebraicSpaces (diag Z)) :
    IsFormalAlgebraicSpace (pullback f g) := sorry

/-- The apex of an `IsPullback` square of morphisms of sheaves into a sheaf
whose diagonal is representable by algebraic spaces is a formal algebraic
space when the two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y}
    (sq : IsPullback fst snd f g)
    (h_diag : representableByAlgebraicSpaces (diag Z)) :
    IsFormalAlgebraicSpace P := sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
