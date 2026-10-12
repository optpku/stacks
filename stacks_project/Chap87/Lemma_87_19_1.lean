/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_19_1_Composition

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Limits ChosenBigFppfSite

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Lemma 87.19.1 (1): The composition of morphisms representable by algebraic
spaces is representable by algebraic spaces. -/
@[stacks 0APY]
theorem representableByAlgebraicSpaces.comp
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : representableByAlgebraicSpaces f) (hg : representableByAlgebraicSpaces g) :
    representableByAlgebraicSpaces (f ≫ g) :=
  sorry

/-- Lemma 87.19.1 (2): The composition of morphisms representable by schemes is
representable by schemes. -/
@[stacks 0APY]
theorem relativelyRepresentable.comp
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f)
    (hg : (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable g) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (f ≫ g) :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
