module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Limits ChosenBigFppfSite

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Lemma 87.19.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. If `f ≫ g : X ⟶ Z` is
representable by algebraic spaces, then `f : X ⟶ Y` is representable by
algebraic spaces. -/
@[stacks 0AQ0]
theorem representableByAlgebraicSpaces.of_comp
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : representableByAlgebraicSpaces (f ≫ g)) :
    representableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
